#!/usr/bin/env python3
"""Heartbeats v0.1: search-v0.3's menu searches with the registered heartbeat limit in force.

  python scripts/run_search_heartbeats.py --dev
  python scripts/run_search_heartbeats.py --register
  python scripts/run_search_heartbeats.py --run [--workers 6]
  python scripts/run_search_heartbeats.py --check-committed

The search registrations state a limit of 40,000 heartbeats per candidate tactic, and the harness sends each
candidate as `set_option maxHeartbeats 40000 in (tac)`. In Lean 4.32 a `set_option` inside a tactic reaches the
kernel but not the elaborator's limit (docs/heartbeat-limit.md), so the candidates elaborated under the limit of the
theorem's context, 200,000 by default. This experiment reruns search-v0.3, the deterministic menu searches on all
1,347 candidate theorems, with the limit in force: each module session defines, right after its imports, a tactic
that runs its argument under an elaborator limit of 40,000 (`withTheReader Core.Context`, `withCurrHeartbeats`), and
every candidate is sent as `set_option maxHeartbeats 40000 in pg_hb_limited (tac)`, so that elaboration and kernel
checks both stop at the registered limit. Everything else is search-v0.3's code, unchanged, each (task, search) unit
in a fresh REPL; the final script is re-verified as before, under the context's limit.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import math
import re
import sys
import threading
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_repl  # noqa: E402
import run_search as v1  # noqa: E402
import run_search_deep as deep  # noqa: E402
import run_search_wide as wide  # noqa: E402
import search_harness as harness  # noqa: E402
from lean_repl import LeanRepl, ReplTimeout  # noqa: E402
from run_linearizations import find_lake, sha256_file, write_lf  # noqa: E402

ROOT = v1.ROOT
EXPERIMENT = ROOT / "experiments" / "heartbeats-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
TASKS = wide.TASKS
V03_RESULTS = wide.RESULTS
IMPLEMENTATIONS = {
    "harness": ROOT / "scripts" / "search_harness.py",
    "repl": ROOT / "scripts" / "lean_repl.py",
    "deepRunner": ROOT / "scripts" / "run_search_deep.py",
    "wideRunner": ROOT / "scripts" / "run_search_wide.py",
    "v1Runner": ROOT / "scripts" / "run_search.py",
    "runner": Path(__file__).resolve(),
}
HEARTBEATS = lean_repl.HEARTBEATS
BUDGET = wide.BUDGET
ARM = wide.ARM
SEARCHES = wide.SEARCHES
LIMIT_DEFINITION = f"""open Lean Elab Tactic in
elab "pg_hb_limited " t:tactic : tactic =>
  withTheReader Core.Context (fun c => {{ c with maxHeartbeats := {HEARTBEATS} * 1000 }}) <| withCurrHeartbeats do
    evalTactic t"""
STOPS = ("maximum number of heartbeats", "deterministic timeout")

QUESTION = ("do the menu searches of search-v0.3, and the comparison between them, come out the same when every "
            "candidate tactic runs under the registered limit of 40,000 heartbeats, in the elaborator as well as in "
            "the kernel")
HYPOTHESES = {
    "H100": "each search proves at least 95% as many tasks under the limit as it proved in search-v0.3",
    "H101": "under the limit, the AND-OR and whole-state searches do not differ significantly: a two-sided sign test "
            "on the tasks exactly one of them proves gives p >= 0.05, as in search-v0.3",
    "H102": "under the limit, the whole-state search's order-duplicate fraction is below 5% and its goal-duplicate "
            "fraction at least twice its order-duplicate fraction, as search-v0.3's H22 and H23 found",
}
CHECKS = {
    "C38": "every unit whose module session was set up defined the limiting tactic",
    "C39": "the limit is reached: at least one candidate application stops on the heartbeat limit",
}


class LimitedRepl(LeanRepl):
    """A REPL session whose candidate tactics run under the limit in the elaborator as well as in the kernel. It
    counts the applications that stop on the limit, by tactic."""

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        self.limit_defined = False
        self.stops: dict[str, int] = {}
        super().__init__(*args, **kwargs)

    def tactic(self, proof_state: int, text: str) -> tuple[list[str], int] | None:
        if re.search(r"\b(sorry|admit)\b", text):
            return None
        if not self.limit_defined:
            raise RuntimeError("the limiting tactic is not defined in this session")
        guarded = f"set_option maxHeartbeats {HEARTBEATS} in pg_hb_limited ({text})"
        response = self._exchange({"tactic": guarded, "proofState": proof_state}, self.timeout)
        errors = [m.get("data", "") for m in response.get("messages", []) if m.get("severity") == "error"]
        errors += [response["message"]] if "message" in response else []
        if any(stop in e for e in errors for stop in STOPS):
            self.stops[text] = self.stops.get(text, 0) + 1
        if "goals" not in response or "proofState" not in response:
            return None
        if errors:
            return None
        if "sorry" in str(response.get("proofStatus", "")):
            return None
        return list(response["goals"]), int(response["proofState"])


class LimitedSession(harness.ModuleSession):
    """A ModuleSession whose environment defines the limiting tactic right after the module's imports."""

    def __init__(self, repl: LimitedRepl, *args: Any, **kwargs: Any) -> None:
        super().__init__(repl, *args, **kwargs)
        response = repl._exchange({"cmd": LIMIT_DEFINITION, "env": self.env}, repl.import_timeout)
        if "env" in response and not any(m.get("severity") == "error" for m in response.get("messages", [])):
            self.env = response["env"]
            repl.limit_defined = True


def run_unit(task: dict[str, Any], search: str, budget: int) -> dict[str, Any]:
    """run_search_deep.run_unit with the limiting session: one menu search on one task in a fresh REPL."""
    head = {"module": task["module"], "declaration": task["declaration"], "arm": ARM, "search": search}
    repl = LimitedRepl(find_lake(), imports=None)
    started = time.monotonic()
    try:
        path = ROOT / ".lake" / "packages" / "mathlib" / (task["module"].replace(".", "/") + ".lean")
        session = LimitedSession(repl, task["module"], path, [(task["declaration"], task["line"])])
        head["limitDefined"] = repl.limit_defined
        if not repl.limit_defined:
            return head | {"constructed": False, "reason": "the limiting tactic did not elaborate"}
        for _, made in session.tasks_in_order():
            if made is None:
                return head | {"constructed": False}
            function = harness.whole_state_search if search == "whole" else harness.and_or_search
            result = function(repl, made.proof_state, [made.goal], harness.menu_proposer, budget,
                              verifier=lambda script, m=made: session.verify(m, script))
            return head | {"constructed": True, "result": result, "stops": dict(sorted(repl.stops.items())),
                           "setupSeconds": round(time.monotonic() - started - result["seconds"], 1)}
        return head | {"constructed": False, "reason": "declaration range not found"}
    except ReplTimeout:
        return head | {"constructed": True, "abandoned": "repl timeout", "stops": dict(sorted(repl.stops.items())),
                       "seconds": round(time.monotonic() - started, 1)}
    finally:
        repl.close()


def run_all(tasks: list[dict[str, Any]], workers: int, budget: int = BUDGET,
            sink: Path | None = RESULTS) -> list[dict[str, Any]]:
    """Every (task, search) unit not yet recorded. An exception raised by a unit is recorded as an error row and retried
    on the next resume."""
    rows: list[dict[str, Any]] = []
    if sink is not None and sink.exists():
        rows = [json.loads(l) for l in sink.read_text(encoding="utf-8").splitlines() if l.strip()]
    done = {(r["module"], r["declaration"], r["search"]) for r in rows if not r.get("error")}
    lock = threading.Lock()

    def guarded(task: dict[str, Any], search: str) -> dict[str, Any]:
        started = time.monotonic()
        try:
            return run_unit(task, search, budget)
        except Exception as error:  # noqa: BLE001
            return {"module": task["module"], "declaration": task["declaration"], "arm": ARM, "search": search,
                    "constructed": None, "error": f"{type(error).__name__}: {error}"[:300],
                    "seconds": round(time.monotonic() - started, 1)}

    def record(row: dict[str, Any]) -> None:
        with lock:
            rows.append(row)
            if sink is not None:
                with sink.open("a", encoding="utf-8", newline="\n") as handle:
                    handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
            result = row.get("result") or {}
            print(json.dumps({"unit": [row["declaration"], row["search"]],
                              "expansions": len(result.get("expansions", [])), "proof": bool(result.get("proof")),
                              "stops": sum((row.get("stops") or {}).values()), "abandoned": row.get("abandoned"),
                              "error": row.get("error"), "at": time.strftime("%H:%M:%S")}), flush=True)

    units = [(t, s) for t in tasks for s in SEARCHES if (t["module"], t["declaration"], s) not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(guarded, t, s) for t, s in units]
        for future in concurrent.futures.as_completed(futures):
            try:
                record(future.result())
            except Exception as error:  # noqa: BLE001
                print(json.dumps({"recordError": f"{type(error).__name__}: {error}"[:300]}), flush=True)
    latest = {(r["module"], r["declaration"], r["search"]): r for r in rows}  # a retried unit keeps its last row
    return list(latest.values())


# Measures

def proved(row: dict[str, Any] | None) -> bool:
    return bool(row and row.get("constructed") and (row.get("result") or {}).get("proof"))


def sign_test_two_sided(k: int, n: int) -> float | None:
    if n == 0:
        return None
    tail = sum(math.comb(n, i) for i in range(0, min(k, n - k) + 1)) / 2 ** n
    return min(1.0, 2 * tail)


def fractions(rows: list[dict[str, Any]]) -> dict[str, Any]:
    expansions = [e for r in rows if r["search"] == "whole" and r.get("result") for e in r["result"]["expansions"]]
    order = sum(1 for e in expansions if e.get("orderDuplicate"))
    goal = sum(1 for e in expansions if e.get("goalDuplicate"))
    return {"expansions": len(expansions), "orderDuplicates": order, "goalDuplicates": goal,
            "orderFraction": order / len(expansions) if expansions else None,
            "goalFraction": goal / len(expansions) if expansions else None}


def summarize(rows: list[dict[str, Any]], tasks: list[dict[str, Any]], v03: list[dict[str, Any]]) -> dict[str, Any]:
    by = {(r["module"], r["declaration"], r["search"]): r for r in rows}
    old = {(r["module"], r["declaration"], r["search"]): r for r in v03}
    keys = [(t["module"], t["declaration"]) for t in tasks]
    posed = [k for k in keys if all((by.get(k + (s,)) or {}).get("constructed") for s in SEARCHES)
             and all((old.get(k + (s,)) or {}).get("constructed") for s in SEARCHES)]
    per_search = {}
    for s in SEARCHES:
        now = [k for k in posed if proved(by.get(k + (s,)))]
        before = [k for k in posed if proved(old.get(k + (s,)))]
        per_search[s] = {"proved": len(now), "provedV03": len(before),
                         "lost": sorted(f"{m}:{d}" for m, d in set(before) - set(now)),
                         "gained": sorted(f"{m}:{d}" for m, d in set(now) - set(before))}
    andor_only = [k for k in posed if proved(by.get(k + ("andor",))) and not proved(by.get(k + ("whole",)))]
    whole_only = [k for k in posed if proved(by.get(k + ("whole",))) and not proved(by.get(k + ("andor",)))]
    p101 = sign_test_two_sided(len(andor_only), len(andor_only) + len(whole_only))
    frac = fractions(rows)
    stops: dict[str, int] = {}
    for r in rows:
        for tactic, n in (r.get("stops") or {}).items():
            stops[tactic] = stops.get(tactic, 0) + n
    setup = [r for r in rows if r.get("limitDefined") is not None]
    return {
        "experiment": "heartbeats-v0.1", "preregistrationSha256": sha256_file(PREREG),
        "units": len(rows), "tasks": len(tasks), "posedInBoth": len(posed),
        "errors": sum(1 for r in rows if r.get("error")), "abandoned": sum(1 for r in rows if r.get("abandoned")),
        "searches": per_search,
        "comparison": {"andorOnly": len(andor_only), "wholeOnly": len(whole_only), "pTwoSided": p101},
        "whole": frac, "stops": {"total": sum(stops.values()), "byTactic": dict(sorted(stops.items()))},
        "hypotheses": {
            "H100": {s: {"proved": per_search[s]["proved"], "provedV03": per_search[s]["provedV03"]}
                     for s in SEARCHES}
                    | {"holds": all(e["proved"] >= 0.95 * e["provedV03"] for e in per_search.values())},
            "H101": {"andorOnly": len(andor_only), "wholeOnly": len(whole_only), "p": p101,
                     "holds": p101 is None or p101 >= 0.05},
            "H102": {"orderFraction": frac["orderFraction"], "goalFraction": frac["goalFraction"],
                     "holds": frac["orderFraction"] is not None and frac["orderFraction"] < 0.05
                     and frac["goalFraction"] >= 2 * frac["orderFraction"]},
        },
        "checks": {
            "C38": {"sessions": len(setup), "undefined": sum(1 for r in setup if not r["limitDefined"]),
                    "holds": all(r["limitDefined"] for r in setup)},
            "C39": {"stops": sum(stops.values()), "holds": sum(stops.values()) > 0},
        },
        "resultsSha256": sha256_file(RESULTS),
    }


def write_report(summary: dict[str, Any]) -> None:
    s = summary
    lines = ["# heartbeats-v0.1", "",
             f"Units: {s['units']}; tasks posed in both experiments: {s['posedInBoth']}; errors {s['errors']}, "
             f"abandoned {s['abandoned']}.", ""]
    for name, e in s["searches"].items():
        lines.append(f"- {name}: {e['proved']} proved under the limit against {e['provedV03']} in search-v0.3; lost "
                     f"{len(e['lost'])}, gained {len(e['gained'])}.")
    c = s["comparison"]
    lines += ["", f"AND-OR only {c['andorOnly']}, whole-state only {c['wholeOnly']}, two-sided p {c['pTwoSided']}.",
              f"Applications stopped on the limit: {s['stops']['total']}.", "", "## Hypotheses", ""]
    for key, entry in s["hypotheses"].items():
        lines.append(f"- {key} ({'holds' if entry['holds'] else 'fails'}): {HYPOTHESES[key]}.")
    lines += ["", "## Checks", ""]
    for key, entry in s["checks"].items():
        lines.append(f"- {key} ({'holds' if entry['holds'] else 'fails'}): {CHECKS[key]}.")
    write_lf(REPORT, "\n".join(lines) + "\n")


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "heartbeats-v0.1",
        "question": QUESTION,
        "tasks": {"source": "search-v0.3", "tasksSha256": sha256_file(TASKS), "count": len(tasks),
                  "rule": "search-v0.3's tasks, all of them, in its order"},
        "comparedResults": {"path": "experiments/search-v0.3/results.jsonl", "sha256": sha256_file(V03_RESULTS)},
        "arm": "menu only, as in search-v0.3",
        "searches": "search-v0.3's whole-state and AND-OR searches, unchanged, run by a copy of run_search_deep.run_unit "
                    "that uses the limiting session",
        "limit": {"definition": LIMIT_DEFINITION, "candidate": f"set_option maxHeartbeats {HEARTBEATS} in "
                                                               "pg_hb_limited (tac)",
                  "placement": "the tactic is defined in each module session right after the module's imports, so "
                               "that the module's own scope cannot capture its names"},
        "budget": {"expansionsPerSearch": BUDGET, "tacticWallClockSeconds": 60, "heartbeats": HEARTBEATS},
        "execution": "every (task, search) unit in a fresh REPL, six units at a time, resumable",
        "measures": {
            "proved": "tasks with a proof that re-verifies from the statement, per search, over the tasks posed in "
                      "both experiments",
            "lostGained": "tasks proved in search-v0.3 and not under the limit, and the reverse, per search",
            "stops": "candidate applications whose error is a heartbeat stop (maximum number of heartbeats, or the "
                     "kernel's deterministic timeout), by tactic",
            "orderFraction, goalFraction": "as in search-v0.3"},
        "hypotheses": HYPOTHESES,
        "checks": CHECKS,
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": DEVELOPMENT_CHECKS,
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


DEVELOPMENT_CHECKS = (
    "scripts/check_tactic_heartbeats.py shows that a tactic setting Core.Context.maxHeartbeats stops the elaborator; "
    "--dev ran the first task's whole-state search at budget 4 under the limiting session: the tactic defined, the "
    "search ran; no other unit was run")


def verify_frozen() -> None:
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["tasks"]["tasksSha256"] != sha256_file(TASKS):
        raise SystemExit("the tasks changed since registration")
    if prereg["comparedResults"]["sha256"] != sha256_file(V03_RESULTS):
        raise SystemExit("search-v0.3's results changed since registration")
    for name in ("harness", "repl", "deepRunner", "wideRunner", "v1Runner"):
        if prereg["implementationSha256"][name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    for flag in ("--dev", "--register", "--run", "--check-committed"):
        mode.add_argument(flag, action="store_true")
    parser.add_argument("--workers", type=int, default=6)
    args = parser.parse_args()
    tasks = json.loads(TASKS.read_text(encoding="utf-8"))
    if args.dev:
        row = run_unit(tasks[0], "whole", 4)
        result = row.get("result") or {}
        print(json.dumps({"limitDefined": row.get("limitDefined"), "constructed": row.get("constructed"),
                          "expansions": len(result.get("expansions", [])), "stops": row.get("stops"),
                          "reason": row.get("reason")}))
        return 0
    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(PREREG, json.dumps(registration_payload(tasks), indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0
    verify_frozen()
    v03 = [json.loads(l) for l in V03_RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    if args.run:
        rows = run_all(tasks, args.workers)
        order = {(t["module"], t["declaration"]): i for i, t in enumerate(tasks)}
        rows.sort(key=lambda r: (order[(r["module"], r["declaration"])], SEARCHES.index(r["search"])))
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        summary = summarize(rows, tasks, v03)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({k: {"holds": v["holds"]} for k, v in summary["hypotheses"].items()}))
        return 0
    if not RESULTS.exists():
        print("heartbeats-v0.1: registered, no results yet")
        return 0
    rows = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    if summarize(rows, tasks, v03) != json.loads(SUMMARY.read_text(encoding="utf-8")):
        raise SystemExit("the committed summary does not follow from the committed results")
    print(f"heartbeats-v0.1-check-ok: units={len(rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
