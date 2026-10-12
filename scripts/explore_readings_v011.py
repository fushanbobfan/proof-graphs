#!/usr/bin/env python3
"""Exploratory, not registered: search-v0.11's paired outcome under other readings of its attempts.

  python scripts/explore_readings_v011.py          # writes experiments/search-v0.11-readings/summary.json
  python scripts/explore_readings_v011.py --check  # recomputes it from the committed rows

search-v0.11 decides on the latest row of each search: a unit in which a search was abandoned or not constructed is
repeated once, both searches with fresh shared draws, and an abandoned search counts as unproved. Its registered test
turns on few tasks, so this recomputes the paired outcome within 48 expansions (cells, one-sided sign test, Newcombe's
interval) on the first attempt of every unit, and with the searches abandoned in the latest rows counted as proved,
for either search or both. It also lists the units that were repeated and, for each task that only one search proves,
what the first attempt gave and whether the group search's proof passed through a group of several goals, and counts
the searches that went on after a REPL restart, which `search_typed_v2` abandons. None of this changes a registered
decision.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_search_confirm as rc  # noqa: E402
import run_search_coupled as v8  # noqa: E402
import run_search_coupled_deep as deep  # noqa: E402
from run_linearizations import sha256_file, write_lf  # noqa: E402

OUT = rc.ROOT / "experiments" / "search-v0.11-readings"
SUMMARY = OUT / "summary.json"
MARK = "counted as proved: the search was abandoned"


def paired(latest: dict[tuple, dict[str, Any]], tasks: list[dict[str, Any]]) -> dict[str, Any]:
    """search-v0.11's paired outcome within its budget, computed as its summary computes it."""
    stated = [t["declaration"] for t in tasks
              if all((latest.get((t["declaration"], s)) or {}).get("constructed") for s in rc.SEARCHES)]
    g = {x for x in stated if deep.proved_within(latest.get((x, "groups")), rc.BUDGET)}
    w = {x for x in stated if deep.proved_within(latest.get((x, "whole")), rc.BUDGET)}
    a, b, c = len(g & w), len(g - w), len(w - g)
    lower, upper = rc.newcombe(a, b, c, len(stated) - a - b - c)
    p = v8.sign_upper(b, b + c)
    return {"stated": len(stated), "proved": {"whole": len(w), "groups": len(g)},
            "cells": {"both": a, "groupsOnly": b, "wholeOnly": c, "neither": len(stated) - a - b - c},
            "difference": (b - c) / len(stated), "newcombe95": [lower, upper], "signTestGroupsMore": p,
            "h109Holds": p is None or p >= rc.ALPHA, "h110Holds": upper < rc.MARGIN}


def outcome(row: dict[str, Any] | None) -> str:
    if row is None:
        return "missing"
    if row.get("error"):
        return "error"
    if row.get("abandoned"):
        return "abandoned"
    if not row.get("constructed"):
        return "not constructed"
    return "proved" if deep.proved_within(row, rc.BUDGET) else "unproved"


def counted_as_proved(latest: dict[tuple, dict[str, Any]], searches: tuple[str, ...]) -> dict[tuple, dict[str, Any]]:
    return {k: (dict(r, result={"proof": [MARK], "expansions": []}) if r.get("abandoned") and k[1] in searches else r)
            for k, r in latest.items()}


def analyse() -> dict[str, Any]:
    rows = rc.read_rows()
    tasks = json.loads(rc.TASKS.read_text(encoding="utf-8"))
    module_of = {t["declaration"]: t["module"] for t in tasks}
    latest = {(r["declaration"], r["search"]): r for r in rows}
    first: dict[tuple, dict[str, Any]] = {}
    attempts: dict[str, int] = {}
    for r in rows:
        first.setdefault((r["declaration"], r["search"]), r)
        if r["search"] == rc.SEARCHES[0]:
            attempts[r["declaration"]] = attempts.get(r["declaration"], 0) + 1

    registered = paired(latest, tasks)
    committed = json.loads(rc.SUMMARY.read_text(encoding="utf-8"))
    for key in ("stated", "cells", "difference", "newcombe95", "signTestGroupsMore"):
        assert registered[key] == committed[key], f"{key} differs from search-v0.11's summary"

    readings = {
        "registered": registered,
        "firstAttempts": paired(first, tasks),
        "abandonedWholeProved": paired(counted_as_proved(latest, ("whole",)), tasks),
        "abandonedGroupsProved": paired(counted_as_proved(latest, ("groups",)), tasks),
        "abandonedBothProved": paired(counted_as_proved(latest, rc.SEARCHES), tasks),
    }
    repeated = sorted(d for d, n in attempts.items() if n > 1)
    after = {"abandonment": 0, "notConstructed": 0}
    for d in repeated:
        firsts = [first[(d, s)] for s in rc.SEARCHES]
        after["abandonment"] += any(r.get("abandoned") for r in firsts)
        after["notConstructed"] += any(r.get("constructed") is False for r in firsts)
    g = set(committed["provedTasks"]["groups"][str(rc.BUDGET)])
    w = set(committed["provedTasks"]["whole"][str(rc.BUDGET)])

    def discordant(names: set[str]) -> list[dict[str, Any]]:
        return [{"declaration": d, "module": module_of[d], "attempts": attempts[d],
                 "firstAttempt": {s: outcome(first[(d, s)]) for s in rc.SEARCHES},
                 "groupsInProof": ((latest[(d, "groups")].get("result") or {}).get("groupsInProof") or 0)}
                for d in sorted(names)]

    # The group search's groups of several goals and its proofs through one, counted as search-v0.10's summary does.
    grouped = [r["result"] for (_, s), r in latest.items() if s == "groups" and r.get("result")]

    return {
        "note": "exploratory, not registered: search-v0.11's paired outcome within 48 expansions on the first attempt "
                "of each unit, and with the searches abandoned in the latest rows counted as proved",
        "readings": readings,
        "allReadings": {"maxUpper": max(r["newcombe95"][1] for r in readings.values()),
                        "minDifference": min(r["difference"] for r in readings.values()),
                        "h109Holds": sorted(k for k, r in readings.items() if r["h109Holds"])},
        "abandonedLatest": [{"declaration": d, "search": s, "attempts": attempts[d]}
                            for (d, s), r in sorted(latest.items()) if r.get("abandoned")],
        "abandonedAttempts": sum(1 for r in rows if r.get("abandoned")),
        # a search that went on after its REPL session was restarted, as in search-v0.10 before amendment 1
        "restartedNotAbandoned": sum(1 for r in rows if (r.get("result") or {}).get("restarts") and not r.get("abandoned")),
        "repeated": {"units": len(repeated), "after": after},
        "groups": {"several": sum(r["groups"]["several"] for r in grouped),
                   "proofsThroughSeveral": sum(1 for r in grouped if r.get("proof") and r.get("groupsInProof"))},
        "groupsOnly": discordant(g - w), "wholeOnly": discordant(w - g),
        "resultsSha256": sha256_file(rc.RESULTS),
    }


def main() -> int:
    out = analyse()
    if "--check" in sys.argv:
        if json.loads(SUMMARY.read_text(encoding="utf-8")) != json.loads(json.dumps(out)):
            raise SystemExit("the committed readings do not follow from search-v0.11's committed rows")
        print(f"search-v0.11-readings-check-ok: H109 holds in {out['allReadings']['h109Holds']}")
        return 0
    OUT.mkdir(parents=True, exist_ok=True)
    write_lf(SUMMARY, json.dumps(out, indent=1) + "\n")
    print(json.dumps({k: {"cells": r["cells"], "p": r["signTestGroupsMore"], "newcombe95": r["newcombe95"]}
                      for k, r in out["readings"].items()}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
