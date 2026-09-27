#!/usr/bin/env python3
"""Goal identity from Lean's expressions, not from printed text.

The text keys of search_keys.py are heuristics in both directions (experiments/goal-key-audit): erasing
metavariable numbers merges goals that differ in which unknowns they share, renaming hypotheses by text
substitution can capture a bound name, and every text key keeps apart goals alike up to the names of bound
variables. Here each goal of a proof state is exported by a `run_tac` block (Lean core, so no import or
declaration is added to the task's environment) as its local context and target, instantiated and serialized
structurally:

- a hypothesis is written by its position in the context (`h0`, `h1`, ...; implementation details skipped), so
  goals alike up to the names of their hypotheses coincide, and no bound name can be captured;
- a bound variable is written by its de Bruijn index and binder names are dropped, so goals alike up to the
  names of bound variables coincide; binder kinds (implicit, instance, ...) are kept;
- every implicit argument, universe level, and coercion is written, as `pp.all` would;
- a metavariable is written by its unique name, which Python renumbers by first occurrence, the goals' own
  metavariables first, so a goal that reuses an unknown differs from one that has two.

From one export, `state_key` identifies a whole goal list (for a search over states), `goal_key` one goal, and
`group_key` a list of goals coupled by metavariables, each renumbering the metavariables it contains. `groups`
partitions a goal list into coupled groups: two goals are coupled when one mentions the other's metavariable or
both mention a third unassigned one. Identity is syntactic on instantiated expressions; goals equal only up to
definitional unfolding stay apart.
"""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any

from lean_repl import LeanRepl, ReplTimeout

HEARTBEATS = 400000
KEY_TACTIC = r"""run_tac do
  let bic : Lean.BinderInfo → String := fun
    | .implicit => "{}" | .strictImplicit => "{{}}" | .instImplicit => "[]" | _ => ""
  let mut goals : Array Lean.Json := #[]
  for g in (← Lean.Elab.Tactic.getGoals) do
    let decl ← g.getDecl
    let mut pos : Std.HashMap Lean.FVarId Nat := {}
    let mut ldecls : Array Lean.LocalDecl := #[]
    for d? in decl.lctx.decls.toArray do
      if let some d := d? then
        if !d.isImplementationDetail then
          pos := pos.insert d.fvarId ldecls.size
          ldecls := ldecls.push d
    let posF := pos
    let ser : Lean.Expr → Lean.MetaM String := fun e0 => do
      let e0 ← Lean.instantiateMVars e0
      let mut out : Array String := #[]
      let mut stack : List (Sum Lean.Expr String) := [Sum.inl e0]
      repeat
        match stack with
        | [] => break
        | item :: rest =>
          stack := rest
          match item with
          | .inr s => out := out.push s
          | .inl e =>
            match e with
            | .bvar i => out := out.push s!"#{i}"
            | .fvar f => out := out.push (match posF.get? f with | some p => s!"h{p}" | none => "h?")
            | .mvar m => out := out.push s!"?[{m.name}]"
            | .sort l => out := out.push s!"(Sort {l})"
            | .const n ls => out := out.push s!"{n}.\{{String.intercalate "," (ls.map toString)}}"
            | .app f a =>
              stack := Sum.inr "(" :: Sum.inl f :: Sum.inr " " :: Sum.inl a :: Sum.inr ")" :: stack
            | .lam _ t b bi =>
              stack := Sum.inr s!"(fun{bic bi} " :: Sum.inl t :: Sum.inr " => " :: Sum.inl b :: Sum.inr ")" :: stack
            | .forallE _ t b bi =>
              stack := Sum.inr s!"(pi{bic bi} " :: Sum.inl t :: Sum.inr " -> " :: Sum.inl b :: Sum.inr ")" :: stack
            | .letE _ t v b _ =>
              stack := Sum.inr "(let " :: Sum.inl t :: Sum.inr " := " :: Sum.inl v :: Sum.inr "; " :: Sum.inl b
                :: Sum.inr ")" :: stack
            | .lit (.natVal n) => out := out.push s!"{n}"
            | .lit (.strVal s) => out := out.push (Lean.Json.str s).compress
            | .mdata _ x => stack := Sum.inl x :: stack
            | .proj s i x => stack := Sum.inr s!"(proj {s} {i} " :: Sum.inl x :: Sum.inr ")" :: stack
      return String.join out.toList
    let hyps ← g.withContext do
      ldecls.mapM fun d => do
        let t ← ser d.type
        match d.value? with
        | some v => return s!"{t} := {← ser v}"
        | none => return t
    let target ← g.withContext (ser decl.type)
    goals := goals.push (Lean.Json.mkObj [("id", Lean.Json.str s!"{g.name}"),
      ("hyps", Lean.toJson hyps), ("target", Lean.Json.str target)])
  Lean.logInfo (Lean.Json.arr goals).compress"""
MVAR = re.compile(r"\?\[([^\]]*)\]")
LEVEL_MVAR = re.compile(r"\?u\.\d+")


def export(repl: LeanRepl, proof_state: int) -> list[dict[str, Any]] | None:
    """The goals of a proof state as the key tactic exports them, or None if it fails."""
    text = f"set_option maxHeartbeats {HEARTBEATS} in\n{KEY_TACTIC}"
    try:
        response = repl._exchange({"tactic": text, "proofState": proof_state}, repl.timeout)
    except ReplTimeout:
        return None
    if any(m.get("severity") == "error" for m in response.get("messages", [])):
        return None
    infos = [m["data"] for m in response.get("messages", []) if m.get("severity") == "info"]
    if len(infos) != 1:
        return None
    try:
        goals = json.loads(infos[0])
    except json.JSONDecodeError:
        return None
    return goals if isinstance(goals, list) else None


def _renumber(goals: list[dict[str, Any]]) -> list[str]:
    """Each goal written with its metavariables numbered by first occurrence, the goals' own first."""
    numbers: dict[str, int] = {}
    for g in goals:
        numbers.setdefault(g["id"], len(numbers))
    levels: dict[str, int] = {}
    out = []
    for g in goals:
        text = "\n".join(g["hyps"]) + "\n|- " + g["target"]
        text = MVAR.sub(lambda m: f"?{numbers.setdefault(m.group(1), len(numbers))}", text)
        out.append(LEVEL_MVAR.sub(lambda m: f"?u{levels.setdefault(m.group(0), len(levels))}", text))
    return out


def _digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def state_key(goals: list[dict[str, Any]]) -> str:
    return _digest("\n\n".join(_renumber(goals)))


def group_key(goals: list[dict[str, Any]]) -> str:
    return state_key(goals)


def goal_key(goal: dict[str, Any]) -> str:
    return state_key([goal])


def mentions(goal: dict[str, Any]) -> set[str]:
    return set(MVAR.findall("\n".join(goal["hyps"]) + "\n" + goal["target"]))


def groups(goals: list[dict[str, Any]]) -> list[list[int]]:
    """Indices of the goals, partitioned into groups coupled by metavariables, in order of first member."""
    parent = list(range(len(goals)))

    def find(i: int) -> int:
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    owner = {g["id"]: i for i, g in enumerate(goals)}
    seen: dict[str, int] = {}
    for i, g in enumerate(goals):
        for m in mentions(g):
            if m in owner:
                parent[find(i)] = find(owner[m])
            if m in seen:
                parent[find(i)] = find(seen[m])
            else:
                seen[m] = i
    out: dict[int, list[int]] = {}
    for i in range(len(goals)):
        out.setdefault(find(i), []).append(i)
    return sorted(out.values(), key=lambda members: members[0])
