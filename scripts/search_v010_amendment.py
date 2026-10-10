#!/usr/bin/env python3
"""search-v0.10, amendment 1: the units whose searches went on in a new, empty REPL session, repeated.

  python scripts/search_v010_amendment.py --write   # amendment-1.json and summary-as-run.json, before any rerun
  python scripts/search_v010_amendment.py --run     # repeats the units, appends their rows, recomputes the summary
  python scripts/search_v010_amendment.py --check   # verifies the amendment against the committed files

Four counted searches of search-v0.10 went on after a REPL restart (scripts/explore_lost_sessions_v010.py). By the
rule fixed before the run ended, a decision that changes when they count as proved means an amendment: they count as
abandoned, and each of their units is repeated once under the registered attempt rule, all three searches in the
rotating order with the set's seeded draws and fresh draws beyond them, run by search_typed_v2.run_one, in which a
lost session abandons the search. The repetition's rows are appended to results.jsonl, marked with the amendment,
and replace the unit's earlier rows by the latest-row rule; its new draws go to amendment-1-draws.jsonl.gz; the
summary and the report are recomputed by search-v0.10's own code. The summary as run is kept beside them.
"""

from __future__ import annotations

import argparse
import gzip
import json
import sys
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import explore_lost_sessions_v010 as lost  # noqa: E402
import run_search_coupled as v8  # noqa: E402
import run_search_coupled_deep as deep  # noqa: E402
import run_search_paired as v6  # noqa: E402
import run_search_typed as rt  # noqa: E402
import search_typed_v2 as guarded  # noqa: E402
import step_prover as prover  # noqa: E402
from run_linearizations import sha256_file, write_lf  # noqa: E402

AMENDMENT = rt.EXPERIMENT / "amendment-1.json"
AS_RUN = rt.EXPERIMENT / "summary-as-run.json"
DRAWS = rt.EXPERIMENT / "amendment-1-draws.jsonl.gz"


def affected() -> list[tuple[int, str]]:
    """The units of the counted searches that went on after a restart, in the rows as run."""
    rows = lost.as_run_rows()
    counted = set(lost.latest_index(rows).values())
    return sorted({(r["replicate"], r["declaration"]) for i, r in enumerate(rows) if i in counted and lost.lost(r)})


def write() -> None:
    if AMENDMENT.exists() or any(r.get("amendment") for r in rt.read_rows()):
        raise SystemExit("amendment 1 is already written")
    analysis = json.loads(lost.SUMMARY.read_text(encoding="utf-8"))
    assert analysis == json.loads(json.dumps(lost.analyse())), "the committed analysis is stale"
    summary = json.loads(rt.SUMMARY.read_text(encoding="utf-8"))
    write_lf(AS_RUN, rt.SUMMARY.read_text(encoding="utf-8"))
    groups = analysis["actual"]["H103"]["tests"]["groupsOverWhole"]
    bound = analysis["bestCase"]["H103"]["tests"]["groupsOverWhole"]
    payload = {
        "amendment": 1,
        "date": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
        "scope": "execution of the units listed below: the tasks, sets, searches, proposer, budgets, measures, "
                 "hypotheses, and analyses are unchanged",
        "observation": "When a REPL request timed out inside an expression export or a verification, the harness "
                       "started a new session and the helper returned None or False, so the search went on in a "
                       "session without the task's environment or its proof states: each later candidate failed, and "
                       "the search ended unproved instead of abandoned. The registered attempt rule repeats a unit "
                       "once when one of its searches is abandoned; these searches were not recorded as abandoned, so "
                       f"their units were not repeated. {len(analysis['lost'])} counted searches went on in this way, "
                       "all of them goal or group searches, each after one expression export failed.",
        "rule": "fixed on 2026-10-09, before the run ended, and committed with scripts/explore_lost_sessions_v010.py "
                "(proof-graphs da9ab4b): recompute every registered decision with each such search counted as proved "
                "within 48 expansions; if a decision changes, amend search-v0.10 and rerun the affected units",
        "trigger": f"in that best case {', '.join(analysis['changed'])} changes: the group search's one-sided sign test "
                   f"against the whole-state search at 48 expansions goes from p = {groups['p']:.4f} (Holm "
                   f"{groups['adjusted']:.4f}) to p = {bound['p']:.4f} (Holm {bound['adjusted']:.4f}) "
                   "(experiments/search-v0.10-lost-sessions)",
        "change": "the searches count as abandoned; each of their units is repeated once under the registered attempt "
                  "rule, its three searches in the rotating order with the set's seeded draws and fresh draws beyond "
                  "them, run by search_typed_v2.run_one, in which a lost session abandons the search; the repetition's "
                  "rows are appended to results.jsonl with \"amendment\": 1 and replace the unit's earlier rows by the "
                  "latest-row rule, and a repetition that abandons a search again is final; its new draws are in "
                  "amendment-1-draws.jsonl.gz; summary.json and report.md are recomputed by run_search_typed's own "
                  "summarize; summary-as-run.json keeps the summary as run",
        "resultsSeenBeforeAmendment": "the complete summary as run (every hypothesis and check held) and the "
                                      "sensitivity analysis above",
        "affectedUnits": [{"replicate": r, "declaration": d} for r, d in affected()],
        "summaryAsRunSha256": sha256_file(AS_RUN),
        "resultsAsRunSha256": lost.as_run_sha256(),
        "implementationSha256": {"amendmentRunner": sha256_file(Path(__file__).resolve()),
                                 "typedV2": sha256_file(Path(guarded.__file__).resolve()),
                                 "lostSessions": sha256_file(Path(lost.__file__).resolve())},
    }
    assert summary["hypotheses"] and payload["affectedUnits"]
    write_lf(AMENDMENT, json.dumps(payload, indent=1, ensure_ascii=False) + "\n")
    print(json.dumps(payload["affectedUnits"]))


def run() -> None:
    amendment = json.loads(AMENDMENT.read_text(encoding="utf-8"))
    for name, path in (("amendmentRunner", Path(__file__).resolve()), ("typedV2", Path(guarded.__file__).resolve())):
        if amendment["implementationSha256"][name] != sha256_file(path):
            raise SystemExit(f"{name} changed since the amendment was written")
    if not deep.server_alive():
        raise SystemExit(f"the prover does not answer on port {deep.PORT}")
    prover.ENDPOINT = deep.ENDPOINT
    prover.MODEL_LOG = None
    tasks = {t["declaration"]: t for t in v6.tasks()}
    sets = rt.seeds()
    recorded = {(r["replicate"], r["declaration"]) for r in rt.read_rows() if r.get("amendment") == 1}
    new_draws: list[dict[str, Any]] = ([json.loads(l) for l in gzip.decompress(DRAWS.read_bytes()).decode("utf-8")
                                        .splitlines() if l.strip()] if DRAWS.exists() else [])
    for unit in amendment["affectedUnits"]:
        replicate, task = unit["replicate"], tasks[unit["declaration"]]
        if (replicate, task["declaration"]) in recorded:  # repeated already, before an interruption
            continue
        deep.admit()
        draws = v8.ReplicateDraws(sets[replicate].get(task["index"], {}))
        rows = []
        for position, search in enumerate(v8.search_order(task["index"], replicate)):
            budget = rt.budget_of(replicate, search)
            row = guarded.run_one(task, search, draws.proposer(search), budget)
            rows.append(row | {"replicate": replicate, "index": task["index"], "position": position, "budget": budget,
                               "draws": dict(draws.counts.get(search, {"seeded": 0, "shared": 0, "drawn": 0})),
                               "amendment": 1})
        # The prover's server is stopped while the machine's owner plays; a draw made then comes back empty, so the
        # unit is not recorded and can be run again.
        if not deep.server_alive() or any(not e.get("replies") for e in draws.log):
            raise SystemExit(f"the prover stopped answering during {task['declaration']}; nothing of this unit was "
                             "recorded, and --run repeats it")
        new_draws += [{"replicate": replicate, "index": task["index"], "declaration": task["declaration"],
                       "amendment": 1} | e for e in draws.log]
        with rt.RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
            for row in rows:
                handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
        DRAWS.write_bytes(gzip.compress("".join(json.dumps(e, ensure_ascii=False) + "\n" for e in new_draws)
                                        .encode("utf-8"), compresslevel=9, mtime=0))
        print(json.dumps({"replicate": replicate, "task": task["declaration"][:40],
                          "searches": {r["search"]: (len((r.get("result") or {}).get("expansions", [])),
                                                     bool((r.get("result") or {}).get("proof")), r.get("abandoned"))
                                       for r in rows}, "draws": len(draws.log), "at": time.strftime("%H:%M:%S")}),
              flush=True)
    summary = rt.summarize(rt.read_rows(), rt.read_draws())
    write_lf(rt.SUMMARY, json.dumps(summary, indent=1) + "\n")
    rt.write_report(summary)
    print(json.dumps({k: {"holds": v["holds"]} for k, v in summary["hypotheses"].items()}))


def check() -> None:
    amendment = json.loads(AMENDMENT.read_text(encoding="utf-8"))
    assert amendment["summaryAsRunSha256"] == sha256_file(AS_RUN), "summary-as-run.json changed"
    assert amendment["resultsAsRunSha256"] == lost.as_run_sha256(), "the rows as run changed"
    as_run = json.loads(AS_RUN.read_text(encoding="utf-8"))
    recomputed = json.loads(json.dumps(rt.summarize(lost.as_run_rows(), rt.read_draws())))
    assert as_run["resultsSha256"] == lost.as_run_sha256()
    recomputed["resultsSha256"] = as_run["resultsSha256"]
    assert recomputed == as_run, "summary-as-run.json does not follow from the rows as run"
    units = {(u["replicate"], u["declaration"]) for u in amendment["affectedUnits"]}
    added = [r for r in rt.read_rows() if r.get("amendment") == 1]
    assert {(r["replicate"], r["declaration"]) for r in added} == units, "the amendment's rows cover other units"
    assert len(added) == len(units) * len(rt.SEARCHES), "each affected unit is repeated once, all three searches"
    latest = lost.latest_index(rt.read_rows())
    rows = rt.read_rows()
    assert all(rows[latest[(r, d, s)]].get("amendment") == 1 for r, d in units for s in rt.SEARCHES)
    print(f"search-v0.10-amendment-1-check-ok: {len(units)} units repeated")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    for flag in ("--write", "--run", "--check"):
        mode.add_argument(flag, action="store_true")
    args = parser.parse_args()
    if args.write:
        write()
    elif args.run:
        run()
    else:
        check()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
