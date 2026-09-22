#!/usr/bin/env python3
"""Best-first tactic search over Lean proof states, instrumented for redundancy.

A task is a Mathlib theorem stated as an `example` in its original context:
`ModuleSession` elaborates the theorem's module up to the theorem, so that
the search sees the same environment the proof was written in and not the
theorem itself (`make_task` instead restates a library theorem as
`example : type_of% @name` in a full-Mathlib environment, for smoke tests).
The whole-state search keeps
the full goal list as its state, applies every candidate tactic of the
proposer to the first goal through the Lean REPL, deduplicates exactly equal
states (the standard practice), and records for every expansion whether

- the state's goal multiset had already been expanded in another order
  (order redundancy), and
- the state's first goal, canonicalized, had already been expanded as the
  first goal of another state (goal sharing, what an AND-OR search over goals
  removes).

Proposers: `menu` (a fixed list of tactics) and `model` (a local
OpenAI-compatible chat endpoint sampled several times, plus the menu). A found
proof is re-verified as one command from the statement.

  python scripts/search_harness.py --theorems Nat.add_comm List.length_append --proposer menu --budget 16
"""

from __future__ import annotations

import argparse
import json
import re
import time
import urllib.request
from dataclasses import dataclass, field
from typing import Any, Callable

from lean_repl import LeanRepl, ReplTimeout
from run_linearizations import find_lake

MENU = ["simp", "simp_all", "omega", "decide", "rfl", "assumption", "trivial", "aesop", "norm_num", "ring",
        "linarith", "positivity", "constructor", "intro x", "ext x", "exact?", "simp at *", "simp [*]",
        "rcases ‹_ ∧ _› with ⟨h₁, h₂⟩", "left", "right", "use 0", "contradiction", "exfalso", "symm", "push_neg"]
MODEL_ENDPOINT = "http://127.0.0.1:8080/v1/chat/completions"
SYSTEM_PROMPT = ("You are a Lean 4 and Mathlib expert. Reply with exactly one tactic that makes progress on "
                 "the first goal, on a single line, without explanation, backticks, or `by`.")
MODEL_LOG: list[dict[str, Any]] | None = None  # raw prompts and replies, when a runner wants them
IN_PREFIX = re.compile(r"\s*(open|set_option|omit|attribute|unseal|include)\b[^\n]*\bin[ \t]*(?=\n|$)")


def canonical_goal(goal: str) -> str:
    """The goal without its case tag and with metavariable numbers erased."""
    lines = goal.split("\n")
    if lines and lines[0].startswith("case "):
        lines = lines[1:]
    text = "\n".join(lines)
    text = re.sub(r"\?m\.\d+", "?m", text)
    text = re.sub(r"\?u\.\d+", "?u", text)
    text = re.sub(r"_uniq\.\d+", "_uniq", text)
    return text


@dataclass
class State:
    id: int
    proof_state: int
    goals: list[str]
    parent: int | None
    tactic: str | None
    depth: int
    children: list[int] = field(default_factory=list)

    @property
    def ordered_key(self) -> tuple[str, ...]:
        return tuple(canonical_goal(g) for g in self.goals)

    @property
    def multiset_key(self) -> tuple[str, ...]:
        return tuple(sorted(self.ordered_key))

    @property
    def first_goal_key(self) -> str:
        return canonical_goal(self.goals[0]) if self.goals else ""


@dataclass
class Task:
    name: str
    binders: list[str]
    header: str  # `example : type_of% @name := by\n  intro ...`
    goal: str


def binder_names(repl: LeanRepl, name: str) -> list[str] | None:
    snippet = ("#eval show Lean.MetaM Unit from do\n"
               f"  let info ← Lean.getConstInfo `{name}\n"
               "  let .thmInfo _ := info | throwError \"not a theorem\"\n"
               "  Lean.Meta.forallTelescope info.type fun xs _ => do\n"
               "    let names ← xs.mapM fun x => do return (← x.fvarId!.getUserName).toString\n"
               "    Lean.logInfo (Lean.toJson names).compress")
    response = repl.command(snippet)
    for message in response.get("messages", []):
        if message.get("severity") == "info":
            try:
                return list(json.loads(message["data"]))
            except (json.JSONDecodeError, TypeError):
                continue
    return None


def make_task(repl: LeanRepl, name: str) -> tuple[Task, int] | None:
    """The task and the REPL proof state of its introduced statement."""
    binders = binder_names(repl, name)
    if binders is None:
        return None
    forbidden = r"\s()\[\]{}⟨⟩,:.✝«»"
    safe = [b if re.fullmatch(rf"[^{forbidden}\d][^{forbidden}]*", b) else f"b{i}" for i, b in enumerate(binders)]
    intro = f"\n  intro {' '.join(safe)}" if safe else ""
    header = f"example : type_of% @{name} := by{intro}"
    response = repl.command(header + "\n  sorry")
    if any(m.get("severity") == "error" for m in response.get("messages", [])) or not response.get("sorries"):
        return None
    sorry = response["sorries"][0]
    return Task(name, safe, header, sorry["goal"]), int(sorry["proofState"])


def declaration_ranges(repl: LeanRepl, env: int, names: list[str]) -> dict[str, tuple[int, int, int, int]]:
    """Start and end (line, column, 1-based lines) of each declaration in its module."""
    out: dict[str, tuple[int, int, int, int]] = {}
    for name in names:
        snippet = ("#eval show Lean.CoreM Unit from do\n"
                   f"  let some ranges ← Lean.findDeclarationRanges? `{name} | throwError \"no range\"\n"
                   "  Lean.logInfo (Lean.toJson [ranges.range.pos.line, ranges.range.pos.column, "
                   "ranges.range.endPos.line, ranges.range.endPos.column]).compress")
        response = repl._exchange({"cmd": snippet, "env": env}, repl.timeout * 4)
        for message in response.get("messages", []):
            if message.get("severity") == "info":
                try:
                    values = json.loads(message["data"])
                    out[name] = (int(values[0]), int(values[1]), int(values[2]), int(values[3]))
                except (json.JSONDecodeError, TypeError, ValueError, IndexError):
                    continue
    return out


def offset_of(lines: list[str], line: int, column: int) -> int:
    """Character offset of a 1-based line and 0-based column in the joined text."""
    return sum(len(l) + 1 for l in lines[:line - 1]) + column


@dataclass
class ModuleTask:
    name: str
    statement: str  # `example <binders> : <type>`, the declaration's own name and modifiers removed
    goal: str
    proof_state: int
    env: int  # the environment before the declaration


class ModuleSession:
    """The tasks of one module in their original context: the module's imports
    are loaded, the source is elaborated up to each task theorem, the theorem
    is stated with `sorry` in a branch environment, and after the search the
    original declaration is elaborated so that later theorems see it."""

    def __init__(self, repl: LeanRepl, module: str, path: Any, tasks: list[tuple[str, int]]) -> None:
        self.repl = repl
        self.module = module
        self.text = open(path, encoding="utf-8").read()
        self.lines = self.text.split("\n")
        self.tasks = tasks  # (name, line of the root `by`)
        self.errors: list[str] = []
        with_module = repl._exchange({"cmd": f"import {module}"}, repl.import_timeout)
        self.ranges = declaration_ranges(repl, with_module["env"], [name for name, _ in tasks])
        header_end = 0
        for index, line in enumerate(self.lines):
            if re.match(r"(module|prelude|(public |meta |public meta )?import)\b", line):
                header_end = index + 1
        header = "\n".join(self.lines[:header_end])
        response = repl._exchange({"cmd": header}, repl.import_timeout)
        self.env = response["env"]
        self.cursor = offset_of(self.lines, header_end + 1, 0)

    def with_modifiers(self, start: int) -> int:
        """The declaration range starts at its keyword; attributes, the
        docstring, and `open ... in` / `set_option ... in` lines on the
        preceding lines belong to it."""
        while True:
            before = self.text[:start].rstrip()
            line_start = before.rfind("\n") + 1
            last_line = before[line_start:]
            if before.endswith("]") and last_line.lstrip().startswith("@["):
                start = line_start
                continue
            if before.endswith("-/"):
                opener = before.rfind("/--")
                if opener != -1 and "-/" not in before[opener:-2]:
                    start = opener
                    continue
            if IN_PREFIX.match(last_line):
                start = line_start
                continue
            return start

    @staticmethod
    def declaration_head(declaration: str) -> tuple[int, int] | None:
        """The offsets where the `... in` prefixes end and just after
        `theorem name` (or `lemma name`), skipping the docstring, attributes,
        and modifiers that precede the keyword."""
        position = 0
        prefix_end = 0
        while True:
            rest = declaration[position:]
            stripped = rest.lstrip()
            position += len(rest) - len(stripped)
            in_line = IN_PREFIX.match(stripped)
            if in_line:
                position += in_line.end()
                prefix_end = position
                continue
            if stripped.startswith("/--"):
                close = stripped.find("-/")
                if close == -1:
                    return None
                position += close + 2
                continue
            if stripped.startswith("@["):
                close = stripped.find("]")
                if close == -1:
                    return None
                position += close + 1
                continue
            head = re.match(r"((?:private|protected|nonrec|noncomputable)\s+)*(theorem|lemma)\s+\S+", stripped)
            return None if head is None else (prefix_end, position + head.end())

    def elaborate(self, text: str) -> int:
        if text.strip():
            response = self.repl._exchange({"cmd": text, "env": self.env}, self.repl.import_timeout)
            for message in response.get("messages", []):
                if message.get("severity") == "error":
                    self.errors.append(message.get("data", "")[:200])
            self.env = response["env"]
        return self.env

    def tasks_in_order(self) -> Any:
        ordered = sorted(((self.ranges[name], name, by_line) for name, by_line in self.tasks if name in self.ranges))
        for (line, column, end_line, end_column), name, by_line in ordered:
            keyword = offset_of(self.lines, line, column)
            start = self.with_modifiers(keyword)
            end = offset_of(self.lines, end_line, end_column)
            if start < self.cursor:
                continue
            self.elaborate(self.text[self.cursor:start])
            declaration = self.text[start:end]
            by_offset = offset_of(self.lines, by_line, 0) - start
            match = None
            for candidate in re.finditer(r":=\s*by\b", declaration):
                if candidate.end() > by_offset:
                    match = candidate
                    break
            task = None
            head = self.declaration_head(declaration)
            if match is not None and head is not None and head[1] < match.start():
                # an `example`: inside `theorem foo := by ...`, `foo` itself is in scope as a
                # recursive reference and a search would use it
                prefix = declaration[:head[0]].rstrip()
                statement = (prefix + "\n" if prefix else "") + "example" + declaration[head[1]:match.start()]
                response = self.repl._exchange({"cmd": statement + ":= by\n  sorry", "env": self.env},
                                               self.repl.import_timeout)
                sorries = response.get("sorries", [])
                if sorries and not any(m.get("severity") == "error" for m in response.get("messages", [])):
                    task = ModuleTask(name, statement, sorries[0]["goal"], int(sorries[0]["proofState"]), self.env)
            yield name, task
            self.elaborate(declaration)
            self.cursor = end

    def verify(self, task: ModuleTask, tactics: list[str]) -> bool:
        body = task.statement + ":= by" + "".join(f"\n  {t}" for t in tactics)
        try:
            response = self.repl._exchange({"cmd": body, "env": task.env}, self.repl.import_timeout)
        except ReplTimeout:
            return False
        messages = response.get("messages", [])
        return not any(m.get("severity") == "error" for m in messages) and \
            not any("sorry" in m.get("data", "") for m in messages) and not response.get("sorries")


def menu_proposer(state: State) -> list[str]:
    return list(MENU)


def model_candidates(state: State, samples: int, temperature: float, model: str, timeout: float = 120.0) -> list[str]:
    prompt = "\n\n".join(state.goals)
    out: list[str] = []
    for _ in range(samples):
        body = {"model": model, "temperature": temperature, "max_tokens": 64,
                "messages": [{"role": "system", "content": SYSTEM_PROMPT}, {"role": "user", "content": prompt}],
                "chat_template_kwargs": {"enable_thinking": False}}
        request = urllib.request.Request(MODEL_ENDPOINT, data=json.dumps(body).encode("utf-8"),
                                         headers={"Content-Type": "application/json"})
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                reply = json.loads(response.read().decode("utf-8"))
        except Exception:  # noqa: BLE001 - the server's failure is recorded as no candidate
            continue
        text = reply["choices"][0]["message"]["content"].strip()
        if MODEL_LOG is not None:
            MODEL_LOG.append({"model": model, "prompt": prompt, "reply": text,
                              "usage": reply.get("usage")})
        text = text.strip("`").strip()
        if text.startswith("by "):
            text = text[3:]
        line = text.split("\n")[0].strip()
        if line and not line.startswith("·") and not line.startswith("--") and line not in out:
            out.append(line)
    return out


def model_proposer(samples: int, temperature: float, model: str) -> Callable[[State], list[str]]:
    def propose(state: State) -> list[str]:
        candidates = model_candidates(state, samples, temperature, model)
        return candidates + [t for t in MENU if t not in candidates]
    return propose


def whole_state_search(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                       proposer: Callable[[State], list[str]], budget: int) -> dict[str, Any]:
    states: list[State] = [State(0, root_proof_state, root_goals, None, None, 0)]
    frontier: list[int] = [0]
    seen_exact: set[tuple[str, ...]] = {states[0].ordered_key}
    expanded_multisets: dict[tuple[str, ...], set[tuple[str, ...]]] = {}
    expanded_first_goals: set[str] = set()
    expansions: list[dict[str, Any]] = []
    proof: list[str] | None = None
    timeouts = 0
    started = time.monotonic()
    while frontier and len(expansions) < budget and proof is None:
        state = states[frontier.pop(0)]  # breadth first: depth, then discovery order
        order_duplicate = state.multiset_key in expanded_multisets and \
            state.ordered_key not in expanded_multisets[state.multiset_key]
        goal_duplicate = state.first_goal_key in expanded_first_goals
        expanded_multisets.setdefault(state.multiset_key, set()).add(state.ordered_key)
        expanded_first_goals.add(state.first_goal_key)
        candidates = proposer(state)
        valid = 0
        exact_duplicates = 0
        for tactic in candidates:
            result = repl.tactic(state.proof_state, tactic)  # a timeout restarts the REPL: propagate
            if result is None:
                continue
            goals, proof_state = result
            child = State(len(states), proof_state, goals, state.id, tactic, state.depth + 1)
            valid += 1
            if not goals:
                states.append(child)
                state.children.append(child.id)
                proof = []
                cursor: State | None = child
                while cursor is not None and cursor.tactic is not None:
                    proof.append(cursor.tactic)
                    cursor = states[cursor.parent] if cursor.parent is not None else None
                proof.reverse()
                break
            if child.ordered_key in seen_exact:
                exact_duplicates += 1
                continue
            seen_exact.add(child.ordered_key)
            states.append(child)
            state.children.append(child.id)
            frontier.append(child.id)
        expansions.append({"state": state.id, "depth": state.depth, "goals": len(state.goals),
                           "candidates": len(candidates), "valid": valid, "exactDuplicates": exact_duplicates,
                           "orderDuplicate": order_duplicate, "goalDuplicate": goal_duplicate})
    return {"expansions": expansions, "states": len(states), "proof": proof, "timeouts": timeouts,
            "seconds": round(time.monotonic() - started, 1), "restarts": repl.restarts,
            "orderDuplicates": sum(1 for e in expansions if e["orderDuplicate"]),
            "goalDuplicates": sum(1 for e in expansions if e["goalDuplicate"]),
            "uniqueFirstGoals": len(expanded_first_goals)}


@dataclass
class GoalNode:
    key: str
    home: tuple[int, int, int]  # a REPL proof state, the 1-based position of this goal in it, its goal count
    proved_by: tuple[str, list[str]] | None = None  # tactic and child keys
    alternatives: list[tuple[str, list[str]]] = field(default_factory=list)
    expansions: int = 0


def and_or_search(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                  proposer: Callable[[State], list[str]], budget: int) -> dict[str, Any]:
    """Search over canonical goals: a goal is expanded once whatever states it
    appears in, and it is proved when one tactic turns it into proved goals
    only. `pick_goal` brings a goal to the front of the state it was created
    in; the goals behind it are carried along and a candidate that changes
    their number is discarded. Those calls are counted separately."""
    root_key = canonical_goal(root_goals[0])
    nodes: dict[str, GoalNode] = {root_key: GoalNode(root_key, (root_proof_state, 1, len(root_goals)))}
    parents: dict[str, set[str]] = {}
    frontier: list[str] = [root_key]
    expansions: list[dict[str, Any]] = []
    picks = 0
    timeouts = 0
    started = time.monotonic()

    def settle(key: str) -> None:
        node = nodes[key]
        if node.proved_by is not None:
            return
        for tactic, children in node.alternatives:
            if all(nodes[c].proved_by is not None for c in children):
                node.proved_by = (tactic, children)
                for parent in parents.get(key, set()):
                    settle(parent)
                return

    while frontier and len(expansions) < budget and nodes[root_key].proved_by is None:
        key = frontier.pop(0)
        node = nodes[key]
        if node.proved_by is not None:
            continue
        proof_state, position, total = node.home
        if position != 1:
            picked = repl.tactic(proof_state, f"pick_goal {position}")
            picks += 1
            if picked is None:
                continue
            proof_state = picked[1]
            node.home = (proof_state, 1, total)
        carried = total - 1
        candidates = proposer(State(len(expansions), proof_state, [key], None, None, 0))
        node.expansions += 1
        valid = 0
        for tactic in candidates:
            result = repl.tactic(proof_state, tactic)
            if result is None:
                continue
            goals, new_state = result
            if len(goals) < carried:
                continue  # the tactic acted on carried goals
            valid += 1
            child_keys = [canonical_goal(g) for g in goals[:len(goals) - carried]]
            for index, child_key in enumerate(child_keys):
                if child_key not in nodes:
                    nodes[child_key] = GoalNode(child_key, (new_state, index + 1, len(goals)))
                    frontier.append(child_key)
                parents.setdefault(child_key, set()).add(key)
            node.alternatives.append((tactic, child_keys))
            if all(nodes[c].proved_by is not None for c in child_keys):
                node.proved_by = (tactic, child_keys)
                for parent in parents.get(key, set()):
                    settle(parent)
                break
        expansions.append({"goal": key[:80], "candidates": len(candidates), "valid": valid})
    proof = _script(nodes, root_key) if nodes[root_key].proved_by is not None else None
    return {"expansions": expansions, "goals": len(nodes), "proof": proof, "picks": picks, "timeouts": timeouts,
            "seconds": round(time.monotonic() - started, 1), "restarts": repl.restarts}


def _script(nodes: dict[str, GoalNode], key: str) -> list[str]:
    tactic, children = nodes[key].proved_by  # type: ignore[misc]
    lines = [tactic]
    if len(children) == 1:
        lines += _script(nodes, children[0])
    else:
        for child in children:
            child_lines = _script(nodes, child)
            lines.append("· " + child_lines[0])
            lines += ["  " + line for line in child_lines[1:]]
    return lines


def verify_script(repl: LeanRepl, task: Task, tactics: list[str]) -> bool:
    body = task.header + "".join(f"\n  {t}" for t in tactics)
    try:
        response = repl.command(body)
    except ReplTimeout:
        return False
    messages = response.get("messages", [])
    return not any(m.get("severity") == "error" for m in messages) and \
        not any("sorry" in m.get("data", "") for m in messages) and not response.get("sorries")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--theorems", nargs="+", required=True)
    parser.add_argument("--proposer", choices=["menu", "model"], default="menu")
    parser.add_argument("--search", choices=["whole", "andor", "both"], default="both")
    parser.add_argument("--budget", type=int, default=16)
    parser.add_argument("--samples", type=int, default=4)
    parser.add_argument("--model", default="local")
    args = parser.parse_args()
    repl = LeanRepl(find_lake())
    proposer = menu_proposer if args.proposer == "menu" else model_proposer(args.samples, 0.8, args.model)
    try:
        for name in args.theorems:
            made = make_task(repl, name)
            if made is None:
                print(json.dumps({"theorem": name, "task": None}))
                continue
            task, proof_state = made
            report: dict[str, Any] = {"theorem": name, "binders": task.binders}
            if args.search in ("whole", "both"):
                result = whole_state_search(repl, proof_state, [task.goal], proposer, args.budget)
                report["whole"] = {k: v for k, v in result.items() if k != "expansions"} | {
                    "expansions": len(result["expansions"]),
                    "verified": verify_script(repl, task, result["proof"]) if result["proof"] else None}
            if args.search in ("andor", "both"):
                result = and_or_search(repl, proof_state, [task.goal], proposer, args.budget)
                report["andor"] = {k: v for k, v in result.items() if k != "expansions"} | {
                    "expansions": len(result["expansions"]),
                    "verified": verify_script(repl, task, result["proof"]) if result["proof"] else None}
            print(json.dumps(report, ensure_ascii=False))
    finally:
        repl.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
