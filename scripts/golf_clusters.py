#!/usr/bin/env python3
"""The second golf window's branching result with pairs clustered by commit (not registered).

  python scripts/golf_clusters.py            # write experiments/golf-v0.2/clusters.json
  python scripts/golf_clusters.py --check    # recompute and compare with the committed file

H40 of golf-v0.2 counts pairs: among the pairs whose length-adjusted branching differs, the golfed proof branches
more in 137 of 198. Pairs from one commit share an author, a date, and often one systematic change, so they are
not independent. This check, made after a review and outside the registration, repeats the test with commits as
the units (a commit counts for the side most of its differing pairs favour; ties are dropped), and gives a
percentile interval for the pair-level share that resamples commits (2,000 resamples, seed 0), with the median
adjusted difference as an effect size. The adjustment is golf-v0.2's own: each side's branching minus the
slice's median branching at its number of steps.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import statistics
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_golf_replication as g  # noqa: E402

OUT = g.EXPERIMENT / "clusters.json"
RESAMPLES = 2000


def sign_upper(k: int, n: int) -> float | None:
    return None if n == 0 else sum(math.comb(n, i) for i in range(k, n + 1)) / 2 ** n


def analysis() -> dict[str, Any]:
    results = [json.loads(l) for l in g.RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    ok = [r for r in results if r["status"] == "ok"]
    eligible = [r for r in ok if r["before"]["steps"] >= g.MIN_STEPS and r["after"]["steps"] >= g.MIN_STEPS]
    reference = g.structure.references()["branching"]

    def adjusted(side: dict[str, Any]) -> float | None:
        n = min(side["steps"], g.POOL_FROM)
        return None if side["branching"] is None or n not in reference else side["branching"] - reference[n]

    pairs = []
    for r in eligible:
        after, before = adjusted(r["after"]), adjusted(r["before"])
        if after is not None and before is not None and after != before:
            pairs.append((r["commit"], after - before))
    higher = sum(1 for _, d in pairs if d > 0)
    by_commit: dict[str, list[float]] = defaultdict(list)
    for commit, d in pairs:
        by_commit[commit].append(d)
    votes = [sum(1 if d > 0 else -1 for d in ds) for ds in by_commit.values()]
    commits_higher = sum(1 for v in votes if v > 0)
    commits_lower = sum(1 for v in votes if v < 0)
    commits = sorted(by_commit)
    rng = random.Random(0)
    shares = []
    for _ in range(RESAMPLES):
        drawn = [d for c in (rng.choice(commits) for _ in commits) for d in by_commit[c]]
        shares.append(sum(1 for d in drawn if d > 0) / len(drawn))
    shares.sort()
    sizes = sorted((len(v) for v in by_commit.values()), reverse=True)
    return {"note": "not registered: H40 of golf-v0.2 with pairs clustered by commit, after a review of 2026-09-26",
            "pairs": len(pairs), "golfedHigher": higher, "commits": len(commits),
            "largestCommitPairs": sizes[0], "largestFiveCommitsPairs": sum(sizes[:5]),
            "commitVotes": {"higher": commits_higher, "lower": commits_lower,
                            "tied": len(votes) - commits_higher - commits_lower,
                            "signTestHigher": sign_upper(commits_higher, commits_higher + commits_lower)},
            "shareHigher": round(higher / len(pairs), 6),
            "shareInterval95": [round(shares[int(0.025 * RESAMPLES)], 6), round(shares[int(0.975 * RESAMPLES) - 1], 6)],
            "medianAdjustedDifference": round(statistics.median(d for _, d in pairs), 6)}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = analysis()
    if args.check:
        committed = json.loads(OUT.read_text(encoding="utf-8"))
        if committed != json.loads(json.dumps(result)):
            raise SystemExit("the committed clustering check does not follow from the committed results")
        print("golf-clusters-check-ok")
        return 0
    OUT.write_bytes((json.dumps(result, indent=1) + "\n").encode("utf-8"))
    print(json.dumps(result, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
