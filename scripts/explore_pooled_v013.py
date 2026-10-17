#!/usr/bin/env python3
"""Descriptive, as search-v0.13 registered it: the three searches over all three sets of draws of the held-out tasks.

  python scripts/explore_pooled_v013.py          # writes experiments/search-v0.13-pooled/summary.json
  python scripts/explore_pooled_v013.py --check  # recomputes it from the committed rows

search-v0.13's registration pools search-v0.11's set of draws (its whole-state and group searches) and search-v0.12's
independent-goal search, which took that set's candidates, with its own two new sets "only descriptively". This
computes, over the tasks stated in all nine searches, each search's score on a task (the number of the three sets in
which it proves the task within 48 expansions, the latest row of each search counting), the tasks whose scores differ
by direction, the mean difference in proof rate, and a 95% percentile interval resampling modules, for the three
pairs search-v0.13 compares. The sign-test p-values describe; no decision rests on them.
"""

from __future__ import annotations

import json
import random
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_search_confirm as rc  # noqa: E402
import run_search_coupled as v8  # noqa: E402
import run_search_coupled_deep as deep  # noqa: E402
import run_search_goals_holdout as v12  # noqa: E402
import run_search_replicates_holdout as v13  # noqa: E402
from run_linearizations import sha256_file, write_lf  # noqa: E402

OUT = v13.ROOT / "experiments" / "search-v0.13-pooled"
SUMMARY = OUT / "summary.json"
SETS = (0, *v13.REPLICATES)  # set 0 is search-v0.11's draws


def latest(path: Path, key) -> dict[tuple, dict[str, Any]]:
    rows = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
    return {key(r): r for r in rows}


def analyse() -> dict[str, Any]:
    tasks = json.loads(v13.TASKS.read_text(encoding="utf-8"))
    module_of = {t["declaration"]: t["module"] for t in tasks}
    first = latest(rc.RESULTS, lambda r: (r["declaration"], r["search"]))
    goals_first = latest(v12.RESULTS, lambda r: (r["declaration"], r["search"]))
    new = latest(v13.RESULTS, lambda r: (r["replicate"], r["declaration"], r["search"]))

    def unit(search: str, k: int, task: str) -> dict[str, Any] | None:
        if k == 0:
            return (goals_first if search == "goals" else first).get((task, search))
        return new.get((k, task, search))

    stated = [t["declaration"] for t in tasks
              if all((unit(s, k, t["declaration"]) or {}).get("constructed") for s in v13.SEARCHES for k in SETS)]
    proved = {s: {k: {x for x in stated if deep.proved_within(unit(s, k, x), v13.BUDGET)} for k in SETS}
              for s in v13.SEARCHES}
    scores = {s: {x: sum(x in proved[s][k] for k in SETS) for x in stated} for s in v13.SEARCHES}
    by_module: dict[str, list[str]] = {}
    for x in stated:
        by_module.setdefault(module_of[x], []).append(x)
    pairs = {}
    for name, (a, b) in v13.COMPARISONS.items():
        d = {x: scores[a][x] - scores[b][x] for x in stated}
        more, fewer = sum(v > 0 for v in d.values()), sum(v < 0 for v in d.values())
        pairs[name] = {"tasksFirstMore": more, "tasksSecondMore": fewer,
                       "signTestFirstMore": v8.sign_upper(more, more + fewer),
                       "meanRateDifference": sum(d.values()) / (len(d) * len(SETS)),
                       "moduleInterval95": deep.module_interval(
                           by_module, lambda xs, d=d: sum(d[x] for x in xs) / (len(xs) * len(SETS)),
                           random.Random(v13.SEED))}
    return {"descriptiveOnly": "search-v0.13's registration pools these sets only descriptively; no decision rests "
                               "on them",
            "tasks": len(tasks), "stated": len(stated),
            "sets": {"0": "search-v0.11's draws: its whole-state and group searches, and search-v0.12's goal search",
                     "1": "search-v0.13's first new set", "2": "search-v0.13's second new set"},
            "proved": {s: {str(k): len(proved[s][k]) for k in SETS} for s in v13.SEARCHES},
            "pairs": pairs,
            "inputs": {"searchV011ResultsSha256": sha256_file(rc.RESULTS),
                       "searchV012ResultsSha256": sha256_file(v12.RESULTS),
                       "searchV013ResultsSha256": sha256_file(v13.RESULTS)}}


def main() -> int:
    out = analyse()
    if "--check" in sys.argv:
        if json.loads(SUMMARY.read_text(encoding="utf-8")) != json.loads(json.dumps(out)):
            raise SystemExit("the committed pooled description does not follow from the committed rows")
        print(f"search-v0.13-pooled-check-ok: {out['stated']} tasks over {len(SETS)} sets")
        return 0
    OUT.mkdir(parents=True, exist_ok=True)
    write_lf(SUMMARY, json.dumps(out, indent=1) + "\n")
    print(json.dumps({"proved": out["proved"], "pairs": out["pairs"]}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
