#!/usr/bin/env python3
"""Not registered: search-v0.13's comparisons with whole states under other treatments of its abandoned searches.

  python scripts/explore_abandoned_v013.py          # writes experiments/search-v0.13-abandoned/summary.json
  python scripts/explore_abandoned_v013.py --check  # recomputes it from the committed rows

search-v0.13 counts a search that its REPL abandoned in the latest attempt as unproved, as registered; 25 searches
of 11 theorems ended so. This recomputes the goal and group searches' differences in proof rate over whole states,
with search-v0.13's own estimator (per-theorem scores over the two new sets, 95% percentile interval resampling
modules, its seed), as registered and under two other treatments: every abandoned search of the goal or group search
counted as proved while the whole-state search's stay unproved, the case most favourable to the goal-level search;
and the 11 theorems left out. These are bounds on what the convention could change, and no decision rests on them.
"""

from __future__ import annotations

import json
import random
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_search_coupled_deep as deep  # noqa: E402
import run_search_replicates_holdout as v13  # noqa: E402
from run_linearizations import sha256_file, write_lf  # noqa: E402

OUT = v13.ROOT / "experiments" / "search-v0.13-abandoned"
SUMMARY = OUT / "summary.json"
TREATMENTS = ("registered", "favourable", "leftOut")


def analyse() -> dict[str, Any]:
    rows = v13.read_rows()
    tasks = json.loads((v13.EXPERIMENT / "tasks.json").read_text(encoding="utf-8"))
    latest = {(r["replicate"], r["declaration"], r["search"]): r for r in rows}
    module_of = {t["declaration"]: t["module"] for t in tasks}
    stated = [t["declaration"] for t in tasks
              if all((latest.get((k, t["declaration"], s)) or {}).get("constructed") for k in v13.REPLICATES
                     for s in v13.SEARCHES)]
    abandoned = sorted({(k, x, s) for (k, x, s), r in latest.items() if r.get("abandoned") and x in stated})
    affected = {x for (_, x, _) in abandoned}

    def proved(k: int, x: str, s: str, favoured: str | None) -> bool:
        if favoured and (k, x, s) in set(abandoned):
            return s == favoured
        return deep.proved_within(latest.get((k, x, s)), v13.BUDGET)

    pairs: dict[str, Any] = {}
    for name, first in (("goalsOverWhole", "goals"), ("groupsOverWhole", "groups")):
        pairs[name] = {}
        for treatment in TREATMENTS:
            favoured = first if treatment == "favourable" else None
            xs = [x for x in stated if treatment != "leftOut" or x not in affected]
            score = {s: {x: sum(proved(k, x, s, favoured) for k in v13.REPLICATES) for x in xs} for s in (first, "whole")}
            d = {x: score[first][x] - score["whole"][x] for x in xs}
            by_module: dict[str, list[str]] = {}
            for x in xs:
                by_module.setdefault(module_of[x], []).append(x)

            def stat(ys: list[str], d: dict[str, int] = d) -> float:
                return sum(d[y] for y in ys) / (len(ys) * len(v13.REPLICATES))

            pairs[name][treatment] = {"tasks": len(xs), "firstMore": sum(v > 0 for v in d.values()),
                                      "wholeMore": sum(v < 0 for v in d.values()), "meanRateDifference": stat(xs),
                                      "moduleInterval95": deep.module_interval(by_module, stat, random.Random(v13.SEED))}
    return {"source": {"rows": sha256_file(v13.RESULTS), "summary": sha256_file(v13.SUMMARY)},
            "stated": len(stated), "abandoned": len(abandoned), "abandonedTheorems": len(affected),
            "abandonedBySearch": {s: sum(1 for a in abandoned if a[2] == s) for s in v13.SEARCHES}, "pairs": pairs}


def main() -> int:
    out = analyse()
    registered = json.loads(v13.SUMMARY.read_text(encoding="utf-8"))["pairs"]
    for name in out["pairs"]:  # the registered treatment is search-v0.13's own summary
        r = out["pairs"][name]["registered"]
        assert r["meanRateDifference"] == registered[name]["meanRateDifference"], name
        assert r["moduleInterval95"] == registered[name]["moduleInterval95"], name
    if "--check" in sys.argv:
        if json.loads(SUMMARY.read_text(encoding="utf-8")) != json.loads(json.dumps(out)):
            raise SystemExit("the committed sensitivity analysis does not follow from the committed rows")
        print(f"search-v0.13-abandoned-check-ok: {out['abandoned']} abandoned searches of {out['abandonedTheorems']} theorems")
        return 0
    OUT.mkdir(parents=True, exist_ok=True)
    write_lf(SUMMARY, json.dumps(out, indent=1) + "\n")
    print(json.dumps(out["pairs"], indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
