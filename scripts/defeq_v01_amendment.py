#!/usr/bin/env python3
"""Defeq v0.1, amendment 1: two analyses beside the registered decisions.

  python scripts/defeq_v01_amendment.py --write
  python scripts/defeq_v01_amendment.py --check

C32 compares each replay's expanded states, by faithful keys, with keys-v0.1's log of the unit. keys-v0.1 exported
through a `run_tac` block, which failed on every state of ten of the units it recorded, so its log has no faithful key
for them; this run exports through tactics defined after the imports, and where that export succeeds the registered
C32 counts the unit as differing although there is nothing to compare. The first analysis computes C32 over the
states keys-v0.1 keyed, and splits the units the registered check counts as differing into those that differ only at
states keys-v0.1 did not key and the others.

The preregistration describes H93's merge time as hashing and isDefEq, without the elaboration of the printed types;
the registered code hashes each goal in the loop that elaborates it, so the hashing is timed with the elaboration. The
second analysis adds the elaboration and hashing time to the merge time, which bounds the ratio the preregistration
describes from above.

The registered artifacts and decisions are not changed. `--write` writes `amendment-1-results.json` from the
committed results, and `--check` recomputes it.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_defeq_replay as dq  # noqa: E402
from run_linearizations import quantiles, sha256_file, write_lf  # noqa: E402

OUT = dq.EXPERIMENT / "amendment-1-results.json"


def keyed_match(log: dict[str, Any], old: dict[str, Any]) -> tuple[bool, bool]:
    """Whether a replay expanded the same states as keys-v0.1's log of the unit, comparing only the states keys-v0.1
    keyed, and whether an expanded state was left uncompared."""
    new_steps, old_steps = dq.kv.expansions_of(log), dq.kv.expansions_of(old)
    if len(new_steps) != len(old_steps):
        return False, False
    uncompared = False
    for (a, _), (b, _) in zip(new_steps, old_steps):
        before = old["states"][str(b)].get("faithful")
        if before is None:
            uncompared = True
        elif log["states"][str(a)].get("faithful") != before:
            return False, uncompared
    return True, uncompared


def replay_check(rows: list[dict[str, Any]], logs: dict[str, Any], old_logs: dict[str, Any],
                 recorded: dict[tuple[str, ...], Any]) -> dict[str, Any]:
    latest = {tuple(r["unit"]): r for r in rows}
    compared = registered_matched = matched = uncompared_units = 0
    differing: list[str] = []
    only_unkeyed: list[str] = []
    other: list[str] = []
    for u, r in latest.items():
        key = json.dumps(list(u))
        if key not in logs or old_logs.get(key) is None:
            continue
        compared += 1
        same_outcome = recorded.get(u) == r.get("outcome")
        registered = dq.replay_matches(logs[key], old_logs[key]) and same_outcome
        keyed, uncompared = keyed_match(logs[key], old_logs[key])
        keyed = keyed and same_outcome
        registered_matched += registered
        matched += keyed
        uncompared_units += uncompared
        name = f"{u[0]} {u[2]}"
        if not keyed:
            differing.append(name)
        if not registered:
            (only_unkeyed if keyed else other).append(name)
    return {"compared": compared,
            "registered": {"matched": registered_matched,
                           "holds": compared > 0 and registered_matched >= dq.REPLAY_SHARE * compared},
            "onKeyedStates": {"matched": matched, "differing": differing, "unitsWithUncomparedStates": uncompared_units,
                              "holds": compared > 0 and matched >= dq.REPLAY_SHARE * compared},
            "registeredDiffering": {"onlyAtUnkeyedStates": only_unkeyed, "other": other}}


def cost(rows: list[dict[str, Any]], logs: dict[str, Any]) -> dict[str, Any]:
    latest = {tuple(r["unit"]): r for r in rows}
    out: dict[str, Any] = {}
    for family in ("prover", "menu"):
        registered: list[float] = []
        with_elaboration: list[float] = []
        for u, r in latest.items():
            key = json.dumps(list(u))
            if u[0] != family or not r.get("constructed") or key not in logs:
                continue
            merged = logs[key].get("merge") or {}
            if not merged.get("completed") or not r["tacticSeconds"] > 0:
                continue
            registered.append(merged["instances"]["seconds"] / r["tacticSeconds"])
            with_elaboration.append((merged["instances"]["seconds"] + merged["elabSeconds"]) / r["tacticSeconds"])
        q = quantiles(with_elaboration)
        out[family] = {"registered": quantiles(registered), "withElaboration": q,
                       "medianBelowShare": q is not None and q["median"] < dq.COST_SHARE}
    return out


def compute() -> dict[str, Any]:
    rows, logs = dq.read_rows(), dq.read_logs()
    return {"experiment": "defeq-v0.1", "amendment": 1, "resultsSha256": sha256_file(dq.RESULTS),
            "logsSha256": sha256_file(dq.LOGS),
            "C32": replay_check(rows, logs, dq.kv.read_logs(), dq.kv.recorded_outcomes()), "H93": cost(rows, logs)}


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    out = json.loads(json.dumps(compute()))
    if args.write:
        write_lf(OUT, json.dumps(out, indent=1) + "\n")
        print(f"written: {OUT}")
        return 0
    if json.loads(OUT.read_text(encoding="utf-8")) != out:
        raise SystemExit("amendment-1-results.json does not follow from the committed results")
    print(f"defeq-v0.1-amendment-1-check-ok: compared={out['C32']['compared']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
