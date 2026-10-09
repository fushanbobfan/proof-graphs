#!/usr/bin/env python3
"""Theorems proved against Lean candidate applications, not expansions (not registered).

  python scripts/explore_cost_curves.py          # writes experiments/cost-curves/summary.json
  python scripts/explore_cost_curves.py --check  # recomputes it from the committed rows

The search budgets of the experiments count expansions, and an expansion of one design can apply more candidates
than an expansion of another: a free-choice expansion applies every candidate to every open goal, and the goal and
group searches expand a merged goal once where a whole-state search expands it in every state that carries it. This
reads the committed rows and gives, per experiment and search, how many tasks are proved within a budget of candidate
applications per task. A search's applications at its proof are those of the expansions up to and including the one
that found it (goal-selection-v0.1 records the exact count, `stepsAtProof`); the curves stop where a search's own
expansion budget did, so they compare designs at equal work only below the smallest such point.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Callable

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "cost-curves" / "summary.json"
GRID = [2 ** k for k in range(4, 15)]


def rows(name: str) -> list[dict[str, Any]]:
    path = ROOT / "experiments" / name / "results.jsonl"
    return [json.loads(l) for l in path.read_text(encoding="utf-8").splitlines() if l.strip()]


def latest(entries: list[dict[str, Any]], key: tuple[str, ...]) -> list[dict[str, Any]]:
    out: dict[tuple[Any, ...], dict[str, Any]] = {}
    for r in entries:
        out[tuple(r.get(k) for k in key)] = r
    return list(out.values())


def applications_at_proof(result: dict[str, Any]) -> int | None:
    if not result.get("proof"):
        return None
    if result.get("stepsAtProof") is not None:
        return int(result["stepsAtProof"])
    return sum(int(e.get("candidates", 0)) for e in result["expansions"])


def total_applications(result: dict[str, Any]) -> int:
    if result.get("steps") is not None:
        return int(result["steps"])
    return sum(int(e.get("candidates", 0)) for e in result["expansions"])


def curve(units: list[dict[str, Any]]) -> dict[str, Any]:
    at_proof = [applications_at_proof(u["result"]) for u in units]
    spent = sorted(total_applications(u["result"]) for u in units)
    return {"units": len(units), "proved": sum(a is not None for a in at_proof),
            "medianApplicationsSpent": spent[len(spent) // 2] if spent else None,
            "totalApplications": sum(spent),
            "provedWithin": {str(b): sum(a is not None and a <= b for a in at_proof) for b in GRID}}


def experiment(name: str, arm_key: str, keep: Callable | None = None) -> dict[str, Any]:
    entries = [r for r in rows(name) if r.get("constructed") and r.get("result")]
    if keep is not None:
        entries = [r for r in entries if keep(r)]
    key = ("replicate", "module", "declaration", arm_key)
    entries = latest(entries, key)
    out: dict[str, Any] = {}
    for arm in sorted({r[arm_key] for r in entries}):
        groups: dict[Any, list[dict[str, Any]]] = {}
        for r in entries:
            if r[arm_key] == arm:
                groups.setdefault(r.get("replicate", 0), []).append(r)
        out[arm] = {str(rep): curve(units) for rep, units in sorted(groups.items())}
    return out


def summarize() -> dict[str, Any]:
    return {
        "note": "tasks proved within a per-task budget of candidate applications; exploratory, not registered",
        "grid": GRID,
        "search-v0.3": experiment("search-v0.3", "search"),
        "goal-selection-v0.1": experiment("goal-selection-v0.1", "arm", keep=lambda r: r.get("arm") != "firstText"),
        "search-v0.8": experiment("search-v0.8", "search"),
        "search-v0.9": experiment("search-v0.9", "search"),
    }


def main() -> int:
    summary = summarize()
    if "--check" in sys.argv:
        if json.loads(OUT.read_text(encoding="utf-8")) != json.loads(json.dumps(summary)):
            raise SystemExit("the committed cost curves do not follow from the committed rows")
        print("cost-curves-check-ok")
        return 0
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_bytes((json.dumps(summary, indent=1) + "\n").encode("utf-8"))
    print(json.dumps({k: {a: {r: (c["proved"], c["provedWithin"]["256"], c["provedWithin"]["1024"])
                              for r, c in v.items()} for a, v in summary[k].items()}
                      for k in summary if k.startswith(("search", "goal"))}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
