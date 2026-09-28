#!/usr/bin/env python3
"""Exploratory, not registered: search-v0.8 with its declaration-range failures rerun.

  python scripts/explore_range_rerun_v08.py --run --workers 6
  python scripts/explore_range_rerun_v08.py --summarize
  python scripts/explore_range_rerun_v08.py --check

In eleven units of search-v0.8, one or two searches were not constructed because the declaration range was
not found, while another search of the same unit, on the same task, was constructed. Amendment 1 reruns other
setup failures but not this reason, so these eleven tasks drop out of every comparison. This reruns each such
unit once, as the amendment reruns a unit (set 0 with its seeded draws, sets 1 and 2 with fresh draws), and
recomputes the comparisons with the new rows in place of the old. The registered artifacts are not changed.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_search_coupled as rc  # noqa: E402
import step_prover as prover  # noqa: E402
from run_linearizations import sha256_file, write_lf  # noqa: E402

OUT = rc.ROOT / "experiments" / "search-v0.8-range-rerun"
ROWS = OUT / "rows.jsonl"
DRAWS = OUT / "draws.jsonl"
SUMMARY = OUT / "summary.json"
REASON = "declaration range not found"


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(l) for l in path.read_text(encoding="utf-8").splitlines() if l.strip()]


def affected(rows: list[dict[str, Any]]) -> list[tuple[int, str]]:
    units: dict[tuple[int, str], list[dict[str, Any]]] = {}
    for r in rows:
        units.setdefault((r["replicate"], r["declaration"]), []).append(r)
    return sorted(u for u, rs in units.items()
                  if any(r.get("constructed") is False and r.get("reason") == REASON for r in rs)
                  and any(r.get("constructed") for r in rs))


def run(workers: int) -> None:
    if not prover.server_alive():
        raise SystemExit("no model server on 127.0.0.1:8080")
    targets = set(affected(read_jsonl(rc.RESULTS)))
    seeds = rc.keys_replay.recorded_draws()
    todo = [(r, t) for r, t in rc.units() if (r, t["declaration"]) in targets]
    OUT.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, Any]] = []
    draws: list[dict[str, Any]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(rc.run_unit, r, t, seeds.get(t["index"], {}) if r == 0 else {}) for r, t in todo]
        for future in concurrent.futures.as_completed(futures):
            unit_rows, unit_draws = future.result()
            rows.extend(unit_rows)
            draws.extend(unit_draws)
            print(json.dumps({"replicate": unit_rows[0]["replicate"], "task": unit_rows[0]["declaration"][:40],
                              "constructed": {r["search"]: r.get("constructed") for r in unit_rows},
                              "proved": {r["search"]: bool((r.get("result") or {}).get("proof")) for r in unit_rows}},
                             ensure_ascii=False), flush=True)
    rows.sort(key=lambda r: (r["replicate"], r["index"], r["position"]))
    draws.sort(key=lambda e: (e["replicate"], e["index"]))
    write_lf(ROWS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
    write_lf(DRAWS, "".join(json.dumps(e, separators=(",", ":"), ensure_ascii=False) + "\n" for e in draws))


def summarize(write: bool = True) -> dict[str, Any]:
    registered = read_jsonl(rc.RESULTS)
    new = read_jsonl(ROWS)
    rerun = {(r["replicate"], r["declaration"]) for r in new}
    merged = [r for r in registered if (r["replicate"], r["declaration"]) not in rerun] + new
    merged_draws = [e for e in rc.read_draws() if (e["replicate"], e["declaration"]) not in rerun] + read_jsonl(DRAWS)
    before = rc.summarize(registered, rc.read_draws())
    after = rc.summarize(merged, merged_draws)
    out = {
        "experiment": "search-v0.8-range-rerun",
        "registered": False,
        "rerunUnits": sorted([list(u) for u in rerun]),
        "failingAgain": [list(u) for u in affected(merged)],
        "stated": {"registered": before["stated"], "withRerun": after["stated"]},
        "pooled": {"registered": before["pooled"], "withRerun": after["pooled"]},
        "pairs": after["pairs"],
        "holm": after["holm"],
        "registeredResultsSha256": sha256_file(rc.RESULTS),
        "rowsSha256": sha256_file(ROWS),
        "drawsSha256": sha256_file(DRAWS),
    }
    out = json.loads(json.dumps(out))
    if write:
        write_lf(SUMMARY, json.dumps(out, indent=1) + "\n")
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--summarize", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--workers", type=int, default=6)
    args = parser.parse_args()
    if args.check:
        if summarize(write=False) != json.loads(SUMMARY.read_text(encoding="utf-8")):
            raise SystemExit("the committed summary does not follow from the committed rows")
        print("search-v0.8-range-rerun-check-ok")
        return 0
    if args.run:
        run(args.workers)
    out = summarize()
    print(json.dumps({k: out[k] for k in ("stated", "pooled", "failingAgain")}))
    print(json.dumps({name: [p["tasksFirstMore"], p["tasksSecondMore"], p["signTestFirstMore"],
                             out["holm"][name]["adjusted"], out["holm"][name]["rejected"]]
                      for name, p in out["pairs"].items()}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
