#!/usr/bin/env python3
"""Defeq v0.1: what goal identity up to definitional equality adds to the faithful key.

  python scripts/run_defeq_replay.py --develop N
  python scripts/run_defeq_replay.py --replay-check N
  python scripts/run_defeq_replay.py --register
  python scripts/run_defeq_replay.py --run [--workers 3]
  python scripts/run_defeq_replay.py --check-committed

keys-v0.1 re-keyed finished searches by the faithful key of `goal_identity`, which is syntactic, and an exploratory
replay of its conflations (keys-v0.1-conflations) found that most goals the text keys join while the faithful key
keeps them apart are syntactic variants of one term, likely equal up to definitional unfolding but not checked in
Lean. This experiment checks it. It replays keys-v0.1's whole-state units unchanged, search-v0.7's whole-state search
(the step prover, from its recorded draws) on its 200 tasks and search-v0.4's keys arm (the menu) on its 300, and
records every state they reach as keys-v0.1 did; it also prints each distinct goal's closed type (`goal_defeq`). After
each search it merges the unit's distinct goals up to definitional equality, in the manner of Lean's canonicalizer,
at reducible, instances, and default transparency, and times the merge.

The exports run as tactics defined once per task environment, right after the imports (`DefeqSession`), as
search-v0.8's export does; keys-v0.1 ran its export as a `run_tac` block, so check C32 compares every replay with
keys-v0.1's log. `--replay-check` replays the first units of the run without the merge, to test that comparison;
`--develop` runs everything on menu searches of theorems outside the corpus.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import ctypes
import gzip
import hashlib
import json
import os
import random
import sys
import tempfile
import threading
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import goal_defeq as gd  # noqa: E402
import goal_identity as gi  # noqa: E402
import run_key_replay as kv  # noqa: E402
import search_faithful as sf  # noqa: E402
import search_harness as harness  # noqa: E402
import step_prover as prover  # noqa: E402
from lean_repl import LeanRepl, ReplTimeout  # noqa: E402
from recording_repl import RecordingRepl  # noqa: E402
from run_linearizations import find_lake, quantiles, sha256_file, write_lf  # noqa: E402
from search_harness import canonical_goal  # noqa: E402
from search_keys import coarse_goal, digest  # noqa: E402

ROOT = kv.ROOT
EXPERIMENT = ROOT / "experiments" / "defeq-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
LOGS = EXPERIMENT / "logs.jsonl.gz"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "defeq": ROOT / "scripts" / "goal_defeq.py", "identity": ROOT / "scripts" / "goal_identity.py",
    "faithful": ROOT / "scripts" / "search_faithful.py", "recorder": ROOT / "scripts" / "recording_repl.py",
    "keyReplay": ROOT / "scripts" / "run_key_replay.py", "keys": ROOT / "scripts" / "search_keys.py",
    "harness": ROOT / "scripts" / "search_harness.py", "repl": ROOT / "scripts" / "lean_repl.py",
    "draws": ROOT / "scripts" / "common_draws.py", "runner": Path(__file__).resolve()}
MODES = ("reducible", "instances", "default")
MARGIN = 0.02          # H90, H91: the defeq goal-duplicate share exceeds the faithful one by less than two points
COST_SHARE = 0.01      # H93: merging costs less than 1% of the search's tactic time
REPLAY_SHARE = 0.98    # C32
ROUND_TRIP_SHARE = 0.90  # C33
PASS_SHARE = 0.98      # C34
BOOTSTRAP = 2000
SEED = 20261007
MAX_ATTEMPTS = 2
PASS_TIMEOUT = 1800.0
CLOSED_DEFINITION = ("open Lean Elab Tactic in\nelab \"pg_closed_types\" : tactic => do"
                     + gd.CLOSED_TACTIC.replace("run_tac do", "", 1))
START_GATE_GB = 15.0
START_SPACING = 45.0
_start_lock = threading.Lock()


# ---------------------------------------------------------------- recording


class DefeqSession(harness.ModuleSession):
    """A ModuleSession whose environment, right after the module's imports, defines search-v0.8's export tactic and
    the closed-type tactic of `goal_defeq`."""

    def __init__(self, repl: LeanRepl, *args: Any, **kwargs: Any) -> None:
        super().__init__(repl, *args, **kwargs)
        ok = True
        for definition in (sf.DEFINITION, CLOSED_DEFINITION):
            response = repl._exchange({"cmd": definition, "env": self.env}, repl.import_timeout)
            if "env" in response and not any(m.get("severity") == "error" for m in response.get("messages", [])):
                self.env = response["env"]
            else:
                ok = False
        setattr(repl, "fast_export", ok)


class DefeqRecordingRepl(RecordingRepl):
    """keys-v0.1's recording session, exporting through the defined tactics, and printing the closed type of each
    goal the first time its faithful key appears. It also times the candidate tactics apart from the exports."""

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        self.closed: dict[str, dict[str, Any]] = {}
        self.order: list[str] = []
        self.tactic_seconds = 0.0
        self.closed_seconds = 0.0
        self._in_summary = 0.0
        super().__init__(*args, **kwargs)

    def summarize(self, proof_state: int, goals: list[str]) -> dict[str, Any]:
        started = time.monotonic()
        entry: dict[str, Any] = {"default": [digest(canonical_goal(g)) for g in goals],
                                 "coarse": [digest(coarse_goal(g)) for g in goals]}
        exported = sf.export(self, proof_state)
        if exported is None or len(exported) != len(goals):
            self.export_failures += 1
            entry |= {"faithful": None, "state": None, "groups": None}
        else:
            keys = [gi.goal_key(g) for g in exported]
            entry |= {"faithful": keys, "state": gi.state_key(exported), "groups": gi.groups(exported)}
            if any(k not in self.closed for k in keys):
                t = time.monotonic()
                closed = self._closed(proof_state)
                self.closed_seconds += time.monotonic() - t
                for i, key in enumerate(keys):
                    if key not in self.closed:
                        self.order.append(key)
                        self.closed[key] = closed[i] if closed is not None and i < len(closed) else {"failed": True}
        self._in_summary += time.monotonic() - started
        return entry

    def _closed(self, proof_state: int) -> list[dict[str, Any]] | None:
        if not getattr(self, "fast_export", False):
            return gd.closed_types(self, proof_state)
        try:
            response = super()._exchange({"tactic": f"set_option maxHeartbeats {gd.HEARTBEATS} in\npg_closed_types",
                                          "proofState": proof_state}, self.timeout)
        except ReplTimeout:
            return None
        out = gd._info(response)
        return out if isinstance(out, list) else None

    def tactic(self, proof_state: int, text: str) -> tuple[list[str], int] | None:
        started, before = time.monotonic(), self._in_summary
        try:
            return super().tactic(proof_state, text)
        finally:
            self.tactic_seconds += time.monotonic() - started - (self._in_summary - before)


def goal_record(closed: dict[str, Any]) -> dict[str, Any]:
    if closed.get("mvar"):
        return {"status": "mvar"}
    if closed.get("failed") or "pp" not in closed:
        return {"status": "failed"}
    status = closed["rt"] if closed["rt"] in ("exact", "reducible", "differs") else "error"
    return {"status": status, "pp": hashlib.sha256(closed["pp"].encode("utf-8")).hexdigest()[:16],
            "chars": len(closed["pp"])}


def merge(repl: DefeqRecordingRepl, proof_state: int) -> dict[str, Any]:
    """The defeq pass over a unit's distinct goals that round-tripped, in order of first appearance."""
    usable = [k for k in repl.order if repl.closed[k].get("rt") in ("exact", "reducible")]
    folder = Path(tempfile.mkdtemp(prefix="defeq-"))
    path = folder / "entries.json"
    path.write_text(json.dumps([{"pp": repl.closed[k]["pp"], "levels": repl.closed[k]["levels"],
                                 "hyps": repl.closed[k]["hyps"]} for k in usable], ensure_ascii=False),
                    encoding="utf-8")
    started = time.monotonic()
    try:
        out = gd.canonical_classes(repl, proof_state, str(path), PASS_TIMEOUT) if usable else \
            {"elaborated": [], "elabNanos": []} | {m: {"classes": [], "nanos": [], "checks": 0, "accepted": 0,
                                                        "exhausted": 0} for m in MODES}
    finally:
        path.unlink(missing_ok=True)
        folder.rmdir()
    seconds = round(time.monotonic() - started, 2)
    if out is None:
        return {"completed": False, "seconds": seconds, "goals": len(usable)}
    record: dict[str, Any] = {"completed": True, "seconds": seconds, "goals": len(usable),
                              "elaborated": sum(1 for x in out["elaborated"] if x),
                              "elabSeconds": round(sum(out["elabNanos"]) / 1e9, 4)}
    for mode in MODES:
        m = out[mode]
        record[mode] = {"classes": {usable[i]: usable[c] for i, c in enumerate(m["classes"]) if c >= 0 and c != i},
                        "seconds": round(sum(m["nanos"]) / 1e9, 4),
                        "maxSeconds": round(max(m["nanos"], default=0) / 1e9, 4),
                        "checks": m["checks"], "accepted": m["accepted"], "exhausted": m["exhausted"]}
    record["unelaborated"] = [usable[i] for i, x in enumerate(out["elaborated"]) if not x]
    return record


def run_unit(kind: str, task: dict[str, Any], search: str, sets: dict[str, list[list[str]]] | None,
             with_merge: bool = True, budget: int | None = None) -> tuple[dict[str, Any], dict[str, Any] | None]:
    head = {"kind": kind, "module": task["module"], "declaration": task["declaration"], "search": search}
    repl = DefeqRecordingRepl(find_lake(), imports=None)
    started = time.monotonic()
    try:
        path = ROOT / ".lake" / "packages" / "mathlib" / (task["module"].replace(".", "/") + ".lean")
        session = DefeqSession(repl, task["module"], path, [(task["declaration"], task["line"])])
        for _, made in session.tasks_in_order():
            if made is None:
                return head | {"constructed": False}, None
            if kind == "prover":
                proposer = kv.ReplayDraws(sets or {}).proposer(search)
                budget_ = kv.v7.BUDGET if budget is None else budget
            else:
                proposer = kv.keys.menu_proposer
                budget_ = kv.v4.ARMS["keys"]["budget"] if budget is None else budget
            repl.recording = True
            result = kv.FUNCTIONS[search](repl, made.proof_state, [made.goal], proposer, budget_,
                                          verifier=lambda script, m=made: session.verify(m, script))
            repl.recording = False
            log = {"expansions": [{k: e.get(k) for k in ("exactDuplicates", "renamedDuplicates", "goalDuplicate",
                                                         "orderDuplicate", "keys")} for e in result["expansions"]],
                   "events": repl.events, "states": {str(k): v for k, v in repl.states.items()},
                   "goals": {k: goal_record(repl.closed[k]) for k in repl.order}}
            log["merge"] = merge(repl, made.proof_state) if with_merge else None
            return head | {"constructed": True, "outcome": [bool(result["proof"]), len(result["expansions"])],
                           "fastExport": getattr(repl, "fast_export", False), "exportFailures": repl.export_failures,
                           "states": len(repl.states), "goals": len(repl.order),
                           "tacticSeconds": round(repl.tactic_seconds, 2),
                           "closedSeconds": round(repl.closed_seconds, 2),
                           "seconds": round(time.monotonic() - started, 1)}, log
        return head | {"constructed": False, "reason": "declaration range not found"}, None
    except ReplTimeout:
        return head | {"constructed": True, "abandoned": "repl timeout",
                       "seconds": round(time.monotonic() - started, 1)}, None
    finally:
        repl.close()


# ---------------------------------------------------------------- running


def units() -> list[tuple[str, dict[str, Any], str]]:
    return [u for u in kv.units() if u[2] == "whole"]


def _commit_available_gb() -> float | None:
    class Status(ctypes.Structure):
        _fields_ = [("dwLength", ctypes.c_ulong), ("dwMemoryLoad", ctypes.c_ulong),
                    ("ullTotalPhys", ctypes.c_ulonglong), ("ullAvailPhys", ctypes.c_ulonglong),
                    ("ullTotalPageFile", ctypes.c_ulonglong), ("ullAvailPageFile", ctypes.c_ulonglong),
                    ("ullTotalVirtual", ctypes.c_ulonglong), ("ullAvailVirtual", ctypes.c_ulonglong),
                    ("ullAvailExtendedVirtual", ctypes.c_ulonglong)]

    try:
        status = Status()
        status.dwLength = ctypes.sizeof(Status)
        if not ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(status)):  # type: ignore[attr-defined]
            return None
        return status.ullAvailPageFile / 2 ** 30
    except Exception:  # noqa: BLE001 - not on Windows
        return None


def admit() -> None:
    """As search-v0.9's runner: a unit starts once 15 GB of commit charge is left, 45 s after the previous start."""
    _start_lock.acquire()
    while (left := _commit_available_gb()) is not None and left < START_GATE_GB:
        time.sleep(30)
    threading.Timer(START_SPACING, _start_lock.release).start()


def read_rows() -> list[dict[str, Any]]:
    if not RESULTS.exists():
        return []
    return [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]


def read_logs() -> dict[str, Any]:
    if not LOGS.exists():
        return {}
    out = {}
    for line in gzip.decompress(LOGS.read_bytes()).decode("utf-8").splitlines():
        if line.strip():
            entry = json.loads(line)
            out[json.dumps(entry["unit"])] = entry["log"]
    return out


def write_logs(logs: dict[str, Any]) -> None:
    lines = "".join(json.dumps({"unit": json.loads(k), "log": logs[k]}, separators=(",", ":")) + "\n"
                    for k in sorted(logs))
    temporary = LOGS.with_name(LOGS.name + ".tmp")
    temporary.write_bytes(gzip.compress(lines.encode("utf-8"), compresslevel=6, mtime=0))
    os.replace(temporary, LOGS)


def final(rows: list[dict[str, Any]]) -> bool:
    """A unit's attempts are final when the latest neither raised nor was abandoned and its merge completed, or after
    MAX_ATTEMPTS attempts."""
    latest = rows[-1]
    if len(rows) >= MAX_ATTEMPTS:
        return True
    return not latest.get("error") and not latest.get("abandoned") and latest.get("mergeCompleted", True)


def run_all(workers: int) -> None:
    sets = kv.recorded_draws()
    for _ in range(MAX_ATTEMPTS + 1):
        rows = read_rows()
        by_unit: dict[tuple[str, ...], list[dict[str, Any]]] = {}
        for r in rows:
            by_unit.setdefault(tuple(r["unit"]), []).append(r)
        done = {u for u, rs in by_unit.items() if final(rs)}
        todo = [u for u in units() if kv.unit_key(*u) not in done]
        if not todo:
            return
        logs = read_logs()
        lock = threading.Lock()
        prover.MODEL_LOG = None

        def guarded(kind: str, task: dict[str, Any], search: str) -> tuple[dict[str, Any], dict[str, Any] | None]:
            started = time.monotonic()
            admit()
            try:
                return run_unit(kind, task, search, sets.get(task["index"]) if kind == "prover" else None)
            except Exception as error:  # noqa: BLE001
                return {"kind": kind, "module": task["module"], "declaration": task["declaration"], "search": search,
                        "error": f"{type(error).__name__}: {error}"[:300],
                        "seconds": round(time.monotonic() - started, 1)}, None

        def record(unit: tuple[str, dict[str, Any], str], result: tuple[dict[str, Any], dict[str, Any] | None]) -> None:
            row, log = result
            row["unit"] = list(kv.unit_key(*unit))
            if log is not None:
                row["mergeCompleted"] = bool((log.get("merge") or {}).get("completed"))
            with lock:
                if log is not None:
                    logs[json.dumps(row["unit"])] = log
                    write_logs(logs)
                with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                    handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
                print(json.dumps({"unit": row["unit"][2][:40], "kind": row["kind"], "outcome": row.get("outcome"),
                                  "goals": row.get("goals"), "merge": row.get("mergeCompleted"),
                                  "error": row.get("error"), "at": time.strftime("%H:%M:%S")}, ensure_ascii=False),
                      flush=True)

        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            futures = {pool.submit(guarded, *u): u for u in todo}
            for future in concurrent.futures.as_completed(futures):
                record(futures[future], future.result())


# ---------------------------------------------------------------- analysis of one unit


def classes_of(log: dict[str, Any], mode: str) -> dict[str, str]:
    """Each faithful goal key's representative under `mode`; a goal that was not merged is its own."""
    return dict(((log.get("merge") or {}).get(mode) or {}).get("classes", {}))


def state_class(entry: dict[str, Any], classes: dict[str, str]) -> tuple[str, ...] | None:
    """A state's identity up to definitional equality: the classes of its goals in order. A state with a goal that
    carries a metavariable keeps its faithful state key, since metavariable sharing is not in the goals' classes."""
    if entry.get("faithful") is None:
        return None
    if entry.get("groups") is not None and any(len(g) > 1 for g in entry["groups"]):
        return ("state", entry["state"])
    return tuple(classes.get(k, k) for k in entry["faithful"])


def has_mvar_goal(entry: dict[str, Any], goals: dict[str, Any]) -> bool:
    return any(goals.get(k, {}).get("status") == "mvar" for k in entry.get("faithful") or [])


def unit_measures(log: dict[str, Any]) -> dict[str, Any]:
    """Goal duplicates among the expansions, extra state merges among the children, and the printed key's false drops,
    under the faithful key and up to definitional equality."""
    states, goals = log["states"], log["goals"]
    steps = kv.expansions_of(log)
    out: dict[str, Any] = {"expansions": len(steps), "flagged": 0, "goalFaithful": 0,
                           "goal": {m: 0 for m in MODES}, "children": 0, "childrenFlagged": 0,
                           "mergeFaithful": 0, "merge": {m: 0 for m in MODES},
                           "conflations": 0, "conflationsUndefined": 0, "conflationsDefeq": {m: 0 for m in MODES}}
    classes = {m: classes_of(log, m) for m in MODES}
    firsts: dict[str, set[str]] = {"faithful": set()} | {m: set() for m in MODES}
    seen_state: dict[str, set[Any]] = {"faithful": set()} | {m: set() for m in MODES}
    printed_first: dict[tuple[str, ...], dict[str, Any]] = {}

    def remember(entry: dict[str, Any]) -> None:
        seen_state["faithful"].add(entry["state"])
        for m in MODES:
            seen_state[m].add(state_class(entry, classes[m]))

    root = states[str(steps[0][0])] if steps else None
    if root is not None and root.get("faithful") is not None:
        remember(root)
        printed_first[tuple(root["default"])] = root
    for state, children in steps:
        entry = states[str(state)]
        if entry.get("faithful") is not None and entry["faithful"]:
            out["flagged"] += 1
            first = entry["faithful"][0]
            out["goalFaithful"] += first in firsts["faithful"]
            firsts["faithful"].add(first)
            for m in MODES:
                c = classes[m].get(first, first)
                out["goal"][m] += c in firsts[m]
                firsts[m].add(c)
        for child in children:
            c = states[str(child)]
            if not c.get("default"):
                continue  # a closed state
            out["children"] += 1
            if c.get("faithful") is None:
                continue
            out["childrenFlagged"] += 1
            faithful_seen = c["state"] in seen_state["faithful"]
            out["mergeFaithful"] += faithful_seen
            for m in MODES:
                out["merge"][m] += (not faithful_seen) and state_class(c, classes[m]) in seen_state[m]
            earlier = printed_first.get(tuple(c["default"]))
            if earlier is None:
                printed_first[tuple(c["default"])] = c
            elif earlier.get("state") != c["state"]:
                out["conflations"] += 1
                defined = earlier.get("faithful") is not None and not has_mvar_goal(c, goals) \
                    and not has_mvar_goal(earlier, goals) and all(
                        goals.get(k, {}).get("status") in ("exact", "reducible")
                        for k in c["faithful"] + earlier["faithful"])
                if not defined:
                    out["conflationsUndefined"] += 1
                else:
                    for m in MODES:
                        out["conflationsDefeq"][m] += state_class(c, classes[m]) == state_class(earlier, classes[m])
            remember(c)
    return out


def replay_matches(log: dict[str, Any], old: dict[str, Any]) -> bool:
    """Whether a replay expanded the same states, by faithful keys, as keys-v0.1's log of the unit."""
    new_steps, old_steps = kv.expansions_of(log), kv.expansions_of(old)
    if len(new_steps) != len(old_steps):
        return False
    return all(log["states"][str(a)].get("faithful") == old["states"][str(b)].get("faithful")
               for (a, _), (b, _) in zip(new_steps, old_steps))


# ---------------------------------------------------------------- summary


def share(a: int, b: int) -> float | None:
    return None if b == 0 else a / b


def module_interval(values: dict[str, tuple[int, int, int]], modules: dict[str, str],
                    rng: random.Random) -> list[float] | None:
    """95% interval of (sum a - sum b) / sum n over units, resampling modules; values[u] = (a, b, n)."""
    by_module: dict[str, list[str]] = {}
    for unit, module in modules.items():
        by_module.setdefault(module, []).append(unit)
    names = sorted(by_module)
    if not names:
        return None
    draws = []
    for _ in range(BOOTSTRAP):
        chosen = [u for m in (rng.choice(names) for _ in names) for u in by_module[m]]
        n = sum(values[u][2] for u in chosen)
        draws.append(0.0 if n == 0 else (sum(values[u][0] for u in chosen) - sum(values[u][1] for u in chosen)) / n)
    draws.sort()
    return [round(draws[int(0.025 * BOOTSTRAP)], 6), round(draws[int(0.975 * BOOTSTRAP) - 1], 6)]


def summarize(rows: list[dict[str, Any]], logs: dict[str, Any]) -> dict[str, Any]:
    latest = {tuple(r["unit"]): r for r in rows}
    old_logs = kv.read_logs()
    recorded = kv.recorded_outcomes()
    rng = random.Random(SEED)
    out: dict[str, Any] = {"experiment": "defeq-v0.1", "preregistrationSha256": sha256_file(PREREG),
                           "units": len(units()), "attempts": len(rows)}
    families = {"prover": "search-v0.7 whole-state search, step prover", "menu": "search-v0.4 keys arm, menu"}
    compared = matched = 0
    differing: list[str] = []
    goal_status: dict[str, int] = {}
    passes = completed = elaborated = usable = 0
    for family in families:
        members = {u: r for u, r in latest.items() if u[0] == family}
        measured = {u: unit_measures(logs[json.dumps(list(u))]) for u, r in members.items()
                    if r.get("constructed") and json.dumps(list(u)) in logs
                    and (logs[json.dumps(list(u))].get("merge") or {}).get("completed")}
        totals: dict[str, Any] = {k: sum(m[k] for m in measured.values()) for k in
                                  ("expansions", "flagged", "goalFaithful", "children", "childrenFlagged",
                                   "mergeFaithful", "conflations", "conflationsUndefined")}
        for k in ("goal", "merge", "conflationsDefeq"):
            totals[k] = {mode: sum(m[k][mode] for m in measured.values()) for mode in MODES}
        modules = {json.dumps(list(u)): u[1] for u in measured}
        values = {json.dumps(list(u)): (m["goal"]["instances"], m["goalFaithful"], m["flagged"])
                  for u, m in measured.items()}
        n = totals["flagged"]
        entry: dict[str, Any] = {
            "description": families[family], "units": len(members), "measured": len(measured),
            "notConstructed": sum(1 for r in members.values() if r.get("constructed") is False),
            "abandoned": sum(1 for r in members.values() if r.get("abandoned")),
            "errors": sum(1 for r in members.values() if r.get("error")), "totals": totals,
            "goalShare": {"faithful": share(totals["goalFaithful"], n)} | {
                m: share(totals["goal"][m], n) for m in MODES},
            "extraMergeShare": {m: share(totals["merge"][m], totals["childrenFlagged"]) for m in MODES},
            "conflationDefeqShare": {m: share(totals["conflationsDefeq"][m],
                                              totals["conflations"] - totals["conflationsUndefined"]) for m in MODES},
            "goalDifferenceInstances": share(totals["goal"]["instances"] - totals["goalFaithful"], n),
            "goalDifferenceInterval": module_interval(values, modules, rng)}
        costs = []
        for u in measured:
            r, merged = members[u], logs[json.dumps(list(u))]["merge"]
            costs.append({"tactic": r["tacticSeconds"], "merge": merged["instances"]["seconds"],
                          "mergeDefault": merged["default"]["seconds"], "elab": merged["elabSeconds"],
                          "goals": merged["goals"]})
        ratios = [c["merge"] / c["tactic"] for c in costs if c["tactic"] > 0]
        entry["cost"] = {"mergeOverTactic": quantiles(ratios), "mergeSeconds": quantiles([c["merge"] for c in costs]),
                         "mergeDefaultSeconds": quantiles([c["mergeDefault"] for c in costs]),
                         "elabSeconds": quantiles([c["elab"] for c in costs]),
                         "tacticSeconds": quantiles([c["tactic"] for c in costs]),
                         "goalsPerUnit": quantiles([float(c["goals"]) for c in costs]),
                         "checks": {m: sum(logs[json.dumps(list(u))]["merge"][m]["checks"] for u in measured)
                                    for m in MODES},
                         "accepted": {m: sum(logs[json.dumps(list(u))]["merge"][m]["accepted"] for u in measured)
                                      for m in MODES},
                         "exhausted": {m: sum(logs[json.dumps(list(u))]["merge"][m]["exhausted"] for u in measured)
                                       for m in MODES}}
        out[family] = entry
        for u, r in members.items():
            key = json.dumps(list(u))
            if key in logs:
                passes += 1
                merged = logs[key].get("merge") or {}
                completed += bool(merged.get("completed"))
                usable += merged.get("goals", 0)
                elaborated += merged.get("elaborated", 0)
                for g in logs[key]["goals"].values():
                    goal_status[g["status"]] = goal_status.get(g["status"], 0) + 1
                old = old_logs.get(key)
                if old is not None:
                    compared += 1
                    same = replay_matches(logs[key], old) and recorded.get(u) == r.get("outcome")
                    matched += same
                    if not same:
                        differing.append(f"{u[0]} {u[2]}")
    without_mvar = sum(v for k, v in goal_status.items() if k != "mvar")
    round_tripped = goal_status.get("exact", 0) + goal_status.get("reducible", 0)
    out["goalStatus"] = goal_status
    out["C32"] = {"compared": compared, "matched": matched, "differing": differing[:30],
                  "holds": compared > 0 and matched >= REPLAY_SHARE * compared}
    out["C33"] = {"withoutMetavariable": without_mvar, "roundTripped": round_tripped,
                  "holds": without_mvar > 0 and round_tripped >= ROUND_TRIP_SHARE * without_mvar}
    out["C34"] = {"passes": passes, "completed": completed, "usable": usable, "elaborated": elaborated,
                  "holds": passes > 0 and completed >= PASS_SHARE * passes and elaborated >= PASS_SHARE * usable}
    pooled_conflations = sum(out[f]["totals"]["conflations"] - out[f]["totals"]["conflationsUndefined"]
                             for f in families)
    pooled_defeq = sum(out[f]["totals"]["conflationsDefeq"]["instances"] for f in families)
    out["conflations"] = {"defined": pooled_conflations, "defeqInstances": pooled_defeq,
                          "share": share(pooled_defeq, pooled_conflations)}
    medians = {f: (out[f]["cost"]["mergeOverTactic"] or {}).get("median") for f in families}
    out["hypotheses"] = {
        "H90": {"supported": out["prover"]["goalDifferenceInterval"] is not None
                and out["prover"]["goalDifferenceInterval"][1] < MARGIN},
        "H91": {"supported": out["menu"]["goalDifferenceInterval"] is not None
                and out["menu"]["goalDifferenceInterval"][1] < MARGIN},
        "H92": {"supported": pooled_conflations > 0 and pooled_defeq >= 0.5 * pooled_conflations},
        "H93": {"supported": all(v is not None and v < COST_SHARE for v in medians.values())}}
    out["resultsSha256"] = sha256_file(RESULTS)
    out["logsSha256"] = sha256_file(LOGS) if LOGS.exists() else None
    return out


def pct(x: float | None, digits: int = 1) -> str:
    return "n/a" if x is None else f"{100 * x:.{digits}f}%"


def write_report(s: dict[str, Any]) -> None:
    lines = ["# Goal identity up to definitional equality (defeq v0.1)", "",
             "Frozen in `preregistration.json` (SHA-256 `" + s["preregistrationSha256"] + "`).", "",
             "| Units | Expansions | Goal duplicates: faithful / reducible / instances / default | Extra state merges: "
             "reducible / instances / default | Printed-key false drops merged (instances) |",
             "| --- | ---: | --- | --- | --- |"]
    for family in ("prover", "menu"):
        e = s[family]
        g, m, c, t = e["goalShare"], e["extraMergeShare"], e["conflationDefeqShare"], e["totals"]
        lines.append(f"| {e['description']} ({e['measured']} of {e['units']}) | {t['flagged']} | {pct(g['faithful'])} / "
                     f"{pct(g['reducible'])} / {pct(g['instances'])} / {pct(g['default'])} | {pct(m['reducible'], 2)} / "
                     f"{pct(m['instances'], 2)} / {pct(m['default'], 2)} | {t['conflationsDefeq']['instances']} of "
                     f"{t['conflations'] - t['conflationsUndefined']} ({pct(c['instances'])}) |")
    lines += ["", "| Units | Instances minus faithful, goal duplicates (95% interval) | Merge / tactic time, median | "
                  "isDefEq checks (accepted, exhausted) at instances |", "| --- | --- | ---: | --- |"]
    for family in ("prover", "menu"):
        e = s[family]
        k = e["cost"]
        lines.append(f"| {family} | {pct(e['goalDifferenceInstances'], 2)} {e['goalDifferenceInterval']} | "
                     f"{pct((k['mergeOverTactic'] or {}).get('median'), 2)} | {k['checks']['instances']} "
                     f"({k['accepted']['instances']}, {k['exhausted']['instances']}) |")
    lines += ["", f"Goal statuses: {s['goalStatus']}.",
              f"C32: {s['C32']['matched']} of {s['C32']['compared']} replays match keys-v0.1 ({s['C32']['holds']}). "
              f"C33: {s['C33']['roundTripped']} of {s['C33']['withoutMetavariable']} goals without a metavariable "
              f"round-trip ({s['C33']['holds']}). C34: {s['C34']['completed']} of {s['C34']['passes']} passes complete, "
              f"{s['C34']['elaborated']} of {s['C34']['usable']} goals elaborate ({s['C34']['holds']}).", "",
              "## Hypotheses", ""]
    lines += [f"- {k}: supported: {v['supported']}." for k, v in s["hypotheses"].items()]
    write_lf(REPORT, "\n".join(lines) + "\n")


# ---------------------------------------------------------------- registration and entry points


DEVELOPMENT_CHECKS: list[str] = [
    "goal_defeq in a Mathlib REPL on hand-made goals: every closed type round-tripped exactly (universe parameters "
    "included once the round trip declares them); at all three transparencies a beta redex merged with its reduct and "
    "two spellings of one universe level merged, `@id ℕ a` stayed apart from `a` (different hashes, as in Lean's "
    "canonicalizer), and with Nat's instances imported an addition through `AddSemigroup.toAdd` merged with one "
    "through `instAddNat`; `h : P ⊢ Q` stayed apart from `⊢ P → Q`; a goal with a metavariable was marked and not "
    "printed. Three defects were fixed on the way: erasing constants' universe levels before reading their argument "
    "kinds turned type arguments into proofs and collapsed every hash (now the head keeps its levels until its kinds "
    "are read); a test whose instance was missing had elaborated to sorryAx; and a closed type alone joined a goal "
    "with a hypothesis to the goal with that hypothesis not yet introduced, which share one closed type (now the "
    "number of hypotheses is part of the hash)",
    "--develop 3, the menu's whole-state search with the merge on three theorems of the first slice outside both "
    "corpora (seed 13): 40 of 40 distinct goals round-tripped exactly; every merge completed; the instances merge "
    "took 0.1 to 0.4 ms per unit against 6 to 58 s of candidate tactics; units took 56 to 90 s in all. The merges it "
    "made on the first two, inspected side by side, were all the introduced/not-introduced joins of the third defect; "
    "after the fix those two units have no merge beyond the faithful key",
    "--replay-check 4, the first four units of the run replayed without the merge: the three constructed units "
    "expanded the same states, by faithful keys, and reached keys-v0.1's outcomes; PolishSpace.Equiv.measurableEquiv "
    "was not constructed, as in keys-v0.1"]


def registration_payload() -> dict[str, Any]:
    all_units = units()
    return {
        "experiment": "defeq-v0.1",
        "question": "how much does identifying goals up to definitional equality, in the manner of Lean's "
                    "canonicalizer, add to the faithful expression key on the searches keys-v0.1 re-keyed, and at "
                    "what cost",
        "units": {"prover": "keys-v0.1's search-v0.7 whole-state units (step prover, replayed from recorded draws)",
                  "menu": "keys-v0.1's search-v0.4 keys-arm units (the menu's whole-state search at 24 expansions)",
                  "count": len(all_units), "keysV01Logs": sha256_file(kv.LOGS),
                  "keysV01Results": sha256_file(kv.RESULTS)},
        "recording": "keys-v0.1's recording session (recording_repl.py), unchanged except that its exports run as "
                     "tactics defined once per task environment right after the imports: search-v0.8's faithful "
                     "export and goal_defeq's closed-type export, printed the first time a faithful goal key appears",
        "identity": {"faithful": "goal_identity.py's key, as in keys-v0.1",
                     "closedType": "a goal's local context (implementation details skipped) abstracted over its "
                                   "target, binder names replaced, printed with pp.all and raw literals, and elaborated "
                                   "back in the same state: exact, equal up to reducible unfolding, or neither; a "
                                   "goal with a metavariable is not printed",
                     "defeq": "after the search, in the task's root state: each round-tripped goal elaborated, "
                              "beta-reduced, its universe levels normalized, hashed ignoring implicit and proof "
                              "arguments and constants' universe levels as Lean's Meta.Canonicalizer does, and merged "
                              "in order of first appearance into the first earlier goal of its hash that isDefEq "
                              "accepts, separately at reducible, instances, and default transparency, each isDefEq "
                              f"with {gd.DEFEQ_HEARTBEATS} heartbeats; a check that exhausts them counts as unequal",
                     "state": "a state's goals' classes in order; a state with goals coupled by metavariables keeps its "
                              "faithful state key"},
        "measures": {
            "goalShare": "whole-state expansions whose first goal was already a first goal, under the faithful key and "
                         "up to definitional equality at each transparency, over the expansions with an exported key",
            "extraMergeShare": "child states whose class an earlier state of the search had while their faithful "
                               "state key is new, over the children with an exported key",
            "conflations": "the printed key's false drops, as keys-v0.1 counted them (H63): child states whose "
                           "printed state key, by which the search drops duplicates, an earlier state had while their "
                           "faithful state keys differ; the share whose classes agree, over those whose goals all "
                           "round-tripped",
            "cost": "per unit, the time of the instances-transparency merge (hashing and isDefEq, not elaboration of "
                    "the printed types) over the time of the search's candidate tactics; isDefEq checks, accepted, "
                    "and exhausted"},
        "hypotheses": {
            "H90": f"search-v0.7's whole-state units: the goal-duplicate share at instances transparency exceeds the "
                   f"faithful key's by less than {100 * MARGIN:g} points: the upper end of the 95% interval of the "
                   f"difference, resampling modules ({BOOTSTRAP:,} resamples, seed {SEED}), is below "
                   f"{100 * MARGIN:g} points",
            "H91": f"search-v0.4's keys-arm units: the same, below {100 * MARGIN:g} points",
            "H92": "of the printed key's false drops (child states whose printed state key an earlier state had while "
                   "their faithful state keys differ, both states' goals round-tripped), pooled over both sets of "
                   "units, at least half are merged at instances transparency",
            "H93": f"in both sets of units, the median over units of the instances-transparency merge time over the "
                   f"candidate-tactic time is below {COST_SHARE:.0%}"},
        "decisionRule": "each hypothesis is decided on its own, by the criterion it states",
        "checks": {"C32": f"at least {REPLAY_SHARE:.0%} of the units recorded in both reach keys-v0.1's outcome and "
                          f"expand the same states, by faithful keys, in the same order",
                   "C33": f"at least {ROUND_TRIP_SHARE:.0%} of the distinct goals without a metavariable round-trip "
                          f"through their printed closed type (exactly or up to reducible unfolding)",
                   "C34": f"at least {PASS_SHARE:.0%} of the merges complete, and at least {PASS_SHARE:.0%} of the "
                          f"round-tripped goals elaborate again in the merge"},
        "execution": "a unit is one task and search in a fresh REPL; at most three units at a time, each started only "
                     f"while {START_GATE_GB:g} GB of commit charge is left and {START_SPACING:g} s after the previous "
                     "start; a unit that raises, is abandoned by a REPL timeout, or whose merge does not complete runs "
                     f"once more ({MAX_ATTEMPTS} attempts at most), and the latest attempt counts",
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": DEVELOPMENT_CHECKS,
        "resultsSeenBeforeRegistration": "every earlier experiment, including keys-v0.1 and keys-v0.1-conflations in "
                                         "full; the development runs below; no merge had run on a corpus task",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def develop(count: int) -> int:
    """The menu's whole-state search on theorems of the first slice outside both corpora, with the merge."""
    corpus = {t["declaration"] for t in kv.v6.tasks()} | {t["declaration"] for t in kv.menu_tasks()}
    source = ROOT / "experiments" / "search-v0.3" / "tasks.json"
    candidates = [t for t in json.loads(source.read_text(encoding="utf-8")) if t["declaration"] not in corpus]
    for task in random.Random(13).sample(candidates, count):
        row, log = run_unit("menu", task, "whole", None)
        merged = (log or {}).get("merge") or {}
        status: dict[str, int] = {}
        for g in (log or {}).get("goals", {}).values():
            status[g["status"]] = status.get(g["status"], 0) + 1
        print(json.dumps({"task": task["declaration"][:50], "row": {k: row.get(k) for k in
                          ("constructed", "outcome", "states", "goals", "tacticSeconds", "closedSeconds", "seconds",
                           "fastExport", "exportFailures")},
                          "status": status, "merge": {k: merged.get(k) for k in
                                                      ("completed", "seconds", "goals", "elaborated", "elabSeconds")},
                          "modes": {m: {k: (merged.get(m) or {}).get(k) for k in
                                        ("seconds", "maxSeconds", "checks", "accepted", "exhausted")} for m in MODES},
                          "measures": unit_measures(log) if log and merged.get("completed") else None},
                         ensure_ascii=False), flush=True)
    return 0


def replay_check(count: int) -> int:
    """The first units of the run replayed without the merge and compared with keys-v0.1's logs (C32's comparison)."""
    old_logs = kv.read_logs()
    recorded = kv.recorded_outcomes()
    sets = kv.recorded_draws()
    for kind, task, search in units()[:count]:
        row, log = run_unit(kind, task, search, sets.get(task["index"]) if kind == "prover" else None, with_merge=False)
        key = kv.unit_key(kind, task, search)
        old = old_logs.get(json.dumps(list(key)))
        same = None if log is None or old is None else replay_matches(log, old)
        print(json.dumps({"unit": task["declaration"][:50], "kind": kind, "outcome": row.get("outcome"),
                          "recorded": recorded.get(key), "matchesKeysV01": same, "states": row.get("states"),
                          "goals": row.get("goals"), "seconds": row.get("seconds")}, ensure_ascii=False), flush=True)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--develop", type=int, metavar="N")
    mode.add_argument("--replay-check", type=int, metavar="N")
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    parser.add_argument("--workers", type=int, default=3)
    args = parser.parse_args()
    if args.develop:
        return develop(args.develop)
    if args.replay_check:
        return replay_check(args.replay_check)
    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(PREREG, json.dumps(registration_payload(), indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered: {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if args.run:
        for name, path in IMPLEMENTATIONS.items():
            if prereg["implementationSha256"][name] != sha256_file(path):
                raise SystemExit(f"implementation {name} changed since registration")
        run_all(args.workers)
        summary = json.loads(json.dumps(summarize(read_rows(), read_logs())))
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({"defeq-v0.1-run": summary["hypotheses"]}))
        return 0
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["preregistrationSha256"] != sha256_file(PREREG) \
            or summary["logsSha256"] != sha256_file(LOGS):
        raise SystemExit("summary hashes do not match the committed files")
    recomputed = json.loads(json.dumps(summarize(read_rows(), read_logs())))
    for key in ("prover", "menu", "goalStatus", "C32", "C33", "C34", "conflations", "hypotheses"):
        if recomputed[key] != summary[key]:
            raise SystemExit(f"the committed summary does not follow from the committed results ({key})")
    print(f"defeq-v0.1-check-ok: attempts={summary['attempts']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
