#!/usr/bin/env python3
"""A diagnostic after the registered run, not part of it: the two replays of the one task whose replays the REPL's
wall clock abandoned during search-v0.7, run again alone, against search-v0.6's rows.

  python experiments/search-v0.7/diagnostic_replay.py

Writes `diagnostic_replay.json` beside this file. The committed results are not changed.
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / "scripts"))
import run_search_renaming as r  # noqa: E402

NAME = "MultilinearMap.map_update_sum"


def main() -> int:
    task = next(t for t in r.v6.tasks() if t["declaration"] == NAME)
    r.prover.MODEL_LOG = None
    started = time.monotonic()
    rows, log = r.run_task(task, r.seeds_by_task().get(task["index"], {}), searches=r.REPLAYS)
    before = {r.v6.unit_key(x): x for x in
              (json.loads(l) for l in r.SEED_RESULTS.read_text(encoding="utf-8").splitlines() if l.strip())}
    units = [{"search": row["search"], "outcome": r.outcome(row),
              "searchV06": r.outcome(before[(row["module"], row["declaration"], row["search"])]),
              "abandoned": row.get("abandoned"), "draws": row["draws"],
              "seconds": (row.get("result") or {}).get("seconds", row.get("seconds"))} for row in rows]
    out = {"task": NAME, "newDraws": len(log), "units": units, "wallSeconds": round(time.monotonic() - started, 1),
           "reproduces": all(u["outcome"] == u["searchV06"] for u in units) and not log,
           "localDate": time.strftime("%Y-%m-%d")}
    r.write_lf(HERE / "diagnostic_replay.json", json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    print(json.dumps(out, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
