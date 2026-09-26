#!/usr/bin/env python3
"""A sensitivity analysis of search-v0.3, not registered: its error units rerun with the corrected AND-OR search.

  python scripts/search_v03_sensitivity.py [--run]

search-v0.3's AND-OR search could record a goal as its own proof (see `search_keys.py`), and building the proof
script then raised RecursionError; the unit is an error row, which the registered summary counts as not proved.
This script reruns every error unit with `search_keys.and_or_search`, which differs only in setting a goal's
proof once, and recomputes the proof counts and the discordant tasks with those outcomes. With --run it reruns
the units (a REPL is needed) and writes `experiments/search-v0.3/sensitivity.json`; without, it recomputes the
file's analysis from its committed reruns and the committed results.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_search_keys as rsk  # noqa: E402
import run_search_wide as v3  # noqa: E402
from run_linearizations import sha256_file, write_lf  # noqa: E402

OUT = v3.EXPERIMENT / "sensitivity.json"


def analysis(rows: list[dict[str, Any]], reruns: list[dict[str, Any]]) -> dict[str, Any]:
    fixed = {(r["module"], r["declaration"], r["search"]): r for r in reruns}
    proved: dict[str, set[tuple[str, str]]] = {"whole": set(), "andor": set()}
    for row in rows:
        unit = (row["module"], row["declaration"], row["search"])
        result = (fixed[unit] if unit in fixed else row).get("result") or {}
        if result.get("proof"):
            proved[row["search"]].add(unit[:2])
    whole_only, andor_only = proved["whole"] - proved["andor"], proved["andor"] - proved["whole"]
    return {"proved": {s: len(v) for s, v in proved.items()},
            "discordant": {"wholeOnly": len(whole_only), "andorOnly": len(andor_only),
                           "signTestTwoSided": v3.sign_test_two_sided(len(andor_only),
                                                                      len(whole_only) + len(andor_only))},
            "H24WithReruns": len(proved["andor"]) >= len(proved["whole"])}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--run", action="store_true")
    args = parser.parse_args()
    rows = [json.loads(l) for l in v3.RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    tasks = {(t["module"], t["declaration"]): t for t in json.loads(v3.TASKS.read_text(encoding="utf-8"))}
    if args.run:
        reruns = []
        for row in rows:
            if row.get("error"):
                task = tasks[(row["module"], row["declaration"])]
                rerun = rsk.run_unit(task, "keys", row["search"], v3.BUDGET)
                result = rerun.get("result") or {}
                reruns.append({"module": row["module"], "declaration": row["declaration"], "search": row["search"],
                               "registeredError": row["error"], "constructed": rerun.get("constructed"),
                               "result": {"proof": result.get("proof"),
                                          "expansions": len(result.get("expansions", [])),
                                          "entangled": result.get("entangled"), "rejected": result.get("rejected")}})
    else:
        reruns = json.loads(OUT.read_text(encoding="utf-8"))["reruns"]
    out = {"note": "not registered: the error units of search-v0.3 rerun with search_keys.and_or_search, which sets "
                   "a goal's proof once; the registered summary is unchanged",
           "resultsSha256": sha256_file(v3.RESULTS), "reruns": reruns, "analysis": analysis(rows, reruns)}
    if args.run:
        write_lf(OUT, json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    elif json.loads(OUT.read_text(encoding="utf-8")) != json.loads(json.dumps(out)):
        raise SystemExit("the committed sensitivity analysis does not follow from the committed results")
    print(json.dumps(out["analysis"]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
