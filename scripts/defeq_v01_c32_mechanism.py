#!/usr/bin/env python3
"""Exploratory, not registered: why defeq-v0.1's C32 fails.

  python scripts/defeq_v01_c32_mechanism.py --write
  python scripts/defeq_v01_c32_mechanism.py --check

C32 compares each replay with keys-v0.1's log by faithful keys. This asks, from the committed logs, whether the
searches themselves were reproduced (the outcome, the number of expansions, and the printed key of every expanded
state), and whether the expanded states whose faithful keys differ hold a goal with a metavariable, as they must if
the difference is the names of universe metavariables, which the expression key writes as Lean names them. It also
counts the expansions whose first goal has a metavariable, the only ones whose goal-duplicate classification such
names can change. `--write` writes `c32-mechanism.json`; `--check` recomputes it.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_defeq_replay as dq  # noqa: E402
from run_linearizations import sha256_file, write_lf  # noqa: E402

OUT = dq.EXPERIMENT / "c32-mechanism.json"


def compute() -> dict[str, Any]:
    kv = dq.kv
    latest = {tuple(r["unit"]): r for r in dq.read_rows()}
    logs, old_logs, recorded = dq.read_logs(), kv.read_logs(), kv.recorded_outcomes()
    compared = reproduced = 0
    not_reproduced: list[str] = []
    differing_units: list[str] = []
    differing_states = with_metavariable = 0
    without: list[list[Any]] = []
    for u, r in latest.items():
        key = json.dumps(list(u))
        if key not in logs or old_logs.get(key) is None:
            continue
        compared += 1
        new, old = logs[key], old_logs[key]
        ns, os_ = kv.expansions_of(new), kv.expansions_of(old)
        same = recorded.get(u) == r.get("outcome") and len(ns) == len(os_) and all(
            new["states"][str(a)].get("default") == old["states"][str(b)].get("default")
            for (a, _), (b, _) in zip(ns, os_))
        reproduced += same
        if not same:
            not_reproduced.append(f"{u[0]} {u[2]}")
        states = [a for (a, _), (b, _) in zip(ns, os_) if old["states"][str(b)].get("faithful") is not None
                  and new["states"][str(a)].get("faithful") != old["states"][str(b)].get("faithful")]
        if states:
            differing_units.append(f"{u[0]} {u[2]}")
        for a in states:
            differing_states += 1
            goals = new["states"][str(a)].get("faithful") or []
            if any(new["goals"].get(g, {}).get("status") == "mvar" for g in goals):
                with_metavariable += 1
            else:
                without.append([f"{u[0]} {u[2]}", a])
    first_goal: dict[str, dict[str, int]] = {}
    for family in ("prover", "menu"):
        flagged = metavariable = 0
        for u, r in latest.items():
            log = logs.get(json.dumps(list(u)))
            if u[0] != family or log is None or not (log.get("merge") or {}).get("completed"):
                continue
            for s, _ in kv.expansions_of(log):
                goals = log["states"][str(s)].get("faithful")
                if goals:
                    flagged += 1
                    metavariable += log["goals"].get(goals[0], {}).get("status") == "mvar"
        first_goal[family] = {"expansions": flagged, "firstGoalWithMetavariable": metavariable}
    return {"experiment": "defeq-v0.1", "registered": False, "resultsSha256": sha256_file(dq.RESULTS),
            "logsSha256": sha256_file(dq.LOGS), "compared": compared, "searchesReproduced": reproduced,
            "notReproduced": not_reproduced, "unitsWithDifferingKeys": differing_units,
            "differingStates": differing_states, "differingStatesWithMetavariableGoal": with_metavariable,
            "differingStatesWithout": without, "firstGoal": first_goal}


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    out = json.loads(json.dumps(compute()))
    if args.write:
        write_lf(OUT, json.dumps(out, indent=1, ensure_ascii=False) + "\n")
        print(f"written: {OUT}")
        return 0
    if json.loads(OUT.read_text(encoding="utf-8")) != out:
        raise SystemExit("c32-mechanism.json does not follow from the committed results")
    print(f"defeq-v0.1-c32-mechanism-check-ok: reproduced={out['searchesReproduced']} of {out['compared']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
