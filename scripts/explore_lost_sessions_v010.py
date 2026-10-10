#!/usr/bin/env python3
"""Exploratory, not registered: search-v0.10's searches that went on in a new, empty REPL session.

  python scripts/explore_lost_sessions_v010.py          # writes experiments/search-v0.10-lost-sessions/summary.json
  python scripts/explore_lost_sessions_v010.py --check  # recomputes it from the committed rows

When a REPL request timed out inside an expression export or a verification, search-v0.10's harness started a new
session and the helper returned None or False, so the search went on in a session without the task's environment
or its proof states: every later candidate failed, and the search ended unproved instead of abandoned
(`search_typed_v2` explains it; search-v0.11 abandons such a search). This finds those searches among the rows
search-v0.10 counts, the latest row of each search, with a REPL restart and no abandonment, and recomputes every
registered decision with search-v0.10's own summary, each such search counted as proved within 48 expansions: the
best case for the search that lost its session. The rule was fixed before the run ended: if a decision changes,
search-v0.10 is amended and the affected units are rerun. It reads the rows as the run left them: rows that amendment
1 appended are left out, and the hash is of the results as run.
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_search_typed as rt  # noqa: E402
from run_linearizations import write_lf  # noqa: E402

OUT = rt.ROOT / "experiments" / "search-v0.10-lost-sessions"
SUMMARY = OUT / "summary.json"
MARK = "counted as proved: the search lost its REPL session"
HYPOTHESES = ("H103", "H104", "H105", "H106")


def lost(row: dict[str, Any]) -> bool:
    return bool((row.get("result") or {}).get("restarts")) and not row.get("abandoned")


def as_run_lines() -> list[str]:
    """results.jsonl's lines as the run left them: everything before the first row an amendment appended."""
    lines = rt.RESULTS.read_text(encoding="utf-8").splitlines(keepends=True)
    first = next((i for i, l in enumerate(lines) if l.strip() and json.loads(l).get("amendment")), len(lines))
    assert not any(l.strip() and not json.loads(l).get("amendment") for l in lines[first:]), "rows after an amendment"
    return lines[:first]


def as_run_rows() -> list[dict[str, Any]]:
    return [json.loads(l) for l in as_run_lines() if l.strip()]


def as_run_sha256() -> str:
    return hashlib.sha256("".join(as_run_lines()).encode("utf-8")).hexdigest()


def latest_index(rows: list[dict[str, Any]]) -> dict[tuple, int]:
    return {(r["replicate"], r["declaration"], r["search"]): i for i, r in enumerate(rows)}


def best_case(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """The rows, with each counted search that lost its session given a proof within 48 expansions."""
    counted = set(latest_index(rows).values())
    out = []
    for i, r in enumerate(rows):
        if i in counted and lost(r):
            result = dict(r["result"], proof=[MARK], expansions=r["result"]["expansions"][:rt.PREFIX])
            r = dict(r, result=result)
        out.append(r)
    return out


def decisions(summary: dict[str, Any]) -> dict[str, Any]:
    h = summary["hypotheses"]
    return {
        "H103": {"holds": h["H103"]["holds"],
                 "tests": {name: {k: t[k] for k in ("p", "adjusted", "rejected")} for name, t in h["H103"]["tests"].items()}},
        "H104": {"holds": h["H104"]["holds"], "p": h["H104"]["p"]},
        "H105": {"holds": h["H105"]["holds"], "agreement": h["H105"]["agreement"]},
        "H106": {"holds": h["H106"]["holds"]},
        "proved48": summary["proved48"], "proved256": summary["proved256"],
    }


def analyse() -> dict[str, Any]:
    rows, draws = as_run_rows(), rt.read_draws()
    counted = set(latest_index(rows).values())
    found = [r for i, r in enumerate(rows) if i in counted and lost(r)]
    actual, bound = decisions(rt.summarize(rows, draws)), decisions(rt.summarize(best_case(rows), draws))
    return {
        "note": "exploratory, not registered: search-v0.10's counted searches that went on after a REPL restart, and "
                "every registered decision with each of them counted as proved within 48 expansions",
        "lostAttempts": sum(1 for r in rows if lost(r)),
        "lost": [{"replicate": r["replicate"], "declaration": r["declaration"], "search": r["search"],
                  "budget": r.get("budget"), "expansions": len(r["result"]["expansions"]),
                  "restarts": r["result"]["restarts"],
                  "expressionExportFailures": r["result"].get("expressionExportFailures")} for r in found],
        "actual": actual, "bestCase": bound,
        "changed": [k for k in HYPOTHESES if actual[k]["holds"] != bound[k]["holds"]],
        "resultsSha256": as_run_sha256(),
    }


def main() -> int:
    out = analyse()
    if "--check" in sys.argv:
        if json.loads(SUMMARY.read_text(encoding="utf-8")) != json.loads(json.dumps(out)):
            raise SystemExit("the committed analysis does not follow from search-v0.10's committed rows")
        print(f"search-v0.10-lost-sessions-check-ok: lost {len(out['lost'])}, changed {out['changed']}")
        return 0
    OUT.mkdir(parents=True, exist_ok=True)
    write_lf(SUMMARY, json.dumps(out, indent=1) + "\n")
    print(json.dumps({"lost": out["lost"], "changed": out["changed"]}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
