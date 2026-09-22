#!/usr/bin/env python3
"""Search v0.2: the searches of search-v0.1 run eight times deeper.

  python scripts/run_search_deep.py --register
  python scripts/run_search_deep.py --run [--workers 4]
  python scripts/run_search_deep.py --check-committed

The tasks are the search-v0.1 tasks on which at least one of the four
searches used its whole budget of 24 expansions without a proof. Every
(task, arm, search) unit runs once at 192 expansions in a fresh REPL, with
the proposers, searches, and verification of search-v0.1 unchanged
(`scripts/search_harness.py`). Both searches are breadth-first, so the first
b expansions of a run are exactly a run at budget b: one run gives the
measures at 24, 48, 96, and 192 expansions. The menu proposer is
deterministic, so its first 24 expansions must reproduce search-v0.1.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import gzip
import json
import sys
import threading
import time
import urllib.request
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_search as v1  # noqa: E402
import search_harness as harness  # noqa: E402
from lean_repl import LeanRepl, ReplTimeout  # noqa: E402
from run_linearizations import find_lake, sha256_file, write_lf  # noqa: E402

ROOT = v1.ROOT
EXPERIMENT = ROOT / "experiments" / "search-v0.2"
PREREG = EXPERIMENT / "preregistration.json"
TASKS = EXPERIMENT / "tasks.json"
RESULTS = EXPERIMENT / "results.jsonl"
MODEL_CALLS = EXPERIMENT / "model-calls.jsonl.gz"
MODEL_CALLS_PLAIN = EXPERIMENT / "model-calls.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "harness": ROOT / "scripts" / "search_harness.py",
    "repl": ROOT / "scripts" / "lean_repl.py",
    "runner": Path(__file__).resolve(),
}
BUDGET = 192
CHECKPOINTS = (24, 48, 96, 192)
V1_BUDGET = 24
ARMS = ("menu", "model")
SEARCHES = ("whole", "andor")
GROWTH_FACTOR = 2.0
ORDER_CEILING = 0.05
WHOLE_KEYS = ("state", "depth", "goals", "candidates", "valid", "exactDuplicates", "orderDuplicate", "goalDuplicate")
ANDOR_KEYS = ("goal", "candidates", "valid")
CHECK_BUDGET = 4


def amendments() -> list[Path]:
    return sorted(EXPERIMENT.glob("amendment-*.json"), key=lambda p: int(p.stem.split("-")[1]))


def expected_implementation_hashes(prereg: dict[str, Any]) -> dict[str, str]:
    expected = dict(prereg["implementationSha256"])
    for path in amendments():
        expected.update(json.loads(path.read_text(encoding="utf-8")).get("implementationSha256AfterAmendment", {}))
    return expected


def v1_rows() -> list[dict[str, Any]]:
    return [json.loads(l) for l in v1.RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]


def select_tasks() -> list[dict[str, Any]]:
    """search-v0.1 tasks, in its order, on which some search used all 24 expansions without a proof."""
    out = []
    for row in v1_rows():
        if not row.get("task"):
            continue
        exhausted = [f"{a}.{s}" for a in ARMS for s in SEARCHES
                     if len(row[f"{a}.{s}"]["expansions"]) >= V1_BUDGET and row[f"{a}.{s}"]["proof"] is None]
        if exhausted:
            out.append({k: row[k] for k in ("module", "declaration", "line", "steps", "structure", "linearizations")}
                       | {"budgetHitInV1": exhausted})
    return out


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "search-v0.2",
        "question": "do the redundancies measured by search-v0.1, and the comparison of whole-state and AND-OR "
                    "search, change when the searches run eight times deeper",
        "tasks": {"source": "search-v0.1", "v1ResultsSha256": sha256_file(v1.RESULTS),
                  "rule": "the search-v0.1 tasks on which at least one of the four searches used all 24 "
                          "expansions without a proof, in search-v0.1 order",
                  "count": len(tasks)},
        "arms": "those of search-v0.1, unchanged (the menu; the local model sampled four times plus the menu)",
        "searches": "those of search-v0.1 after its amendment 2, unchanged",
        "budget": {"expansionsPerSearch": BUDGET, "checkpoints": list(CHECKPOINTS),
                   "note": "both searches are breadth-first and stop only on a proof, an empty frontier, or the "
                           "budget, so the first b expansions of a run at 192 are a run at budget b"},
        "execution": "every (task, arm, search) unit in a fresh REPL; four units at a time; the model server with "
                     "four parallel slots",
        "measures": "as in search-v0.1, at each checkpoint: order- and goal-duplicate fractions over the "
                    "whole-state expansions within the checkpoint, and tasks proved within it by each search",
        "hypotheses": {
            "H17": f"in both arms the goal-duplicate fraction within 192 expansions is at least {GROWTH_FACTOR:g} "
                   "times the fraction within 24 (on the same runs)",
            "H18": "within 192 expansions the AND-OR search proves at least as many tasks as the whole-state search "
                   "in both arms, and strictly more in at least one",
            "H19": f"in both arms the order-duplicate fraction within 192 expansions is below {ORDER_CEILING:.0%}",
        },
        "checks": {"C1": "for every task, the menu arm's first 24 expansions of each search equal those committed "
                         "by search-v0.1 (expansion records and proof), since the menu proposer is deterministic"},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "the runner was exercised on one task at budget 4; no unit of this "
                                                "corpus was run at a larger budget",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def model_server_alive() -> bool:
    try:
        with urllib.request.urlopen("http://127.0.0.1:8080/v1/models", timeout=5) as response:
            return response.status == 200
    except Exception:  # noqa: BLE001
        return False


def run_unit(task: dict[str, Any], arm: str, search: str, budget: int) -> dict[str, Any]:
    """One search on one task in a fresh REPL."""
    head = {"module": task["module"], "declaration": task["declaration"], "arm": arm, "search": search}
    repl = LeanRepl(find_lake(), imports=None)
    started = time.monotonic()
    try:
        path = ROOT / ".lake" / "packages" / "mathlib" / (task["module"].replace(".", "/") + ".lean")
        session = harness.ModuleSession(repl, task["module"], path, [(task["declaration"], task["line"])])
        for _, made in session.tasks_in_order():
            if made is None:
                return head | {"constructed": False}
            proposer = harness.menu_proposer if arm == "menu" else \
                harness.model_proposer(v1.SAMPLES, v1.TEMPERATURE, v1.MODEL_ID)
            function = harness.whole_state_search if search == "whole" else harness.and_or_search
            result = function(repl, made.proof_state, [made.goal], proposer, budget,
                              verifier=lambda script, m=made: session.verify(m, script))
            return head | {"constructed": True, "result": result,
                           "setupSeconds": round(time.monotonic() - started - result["seconds"], 1)}
        return head | {"constructed": False, "reason": "declaration range not found"}
    except ReplTimeout:
        return head | {"constructed": True, "abandoned": "repl timeout",
                       "seconds": round(time.monotonic() - started, 1)}
    finally:
        repl.close()


def run_all(tasks: list[dict[str, Any]], arms: list[str], budget: int, workers: int,
            sink: Path | None) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    done: set[tuple[str, str, str, str]] = set()
    if sink is not None and sink.exists():
        rows = [json.loads(l) for l in sink.read_text(encoding="utf-8").splitlines() if l.strip()]
        done = {(r["module"], r["declaration"], r["arm"], r["search"]) for r in rows}
    model_log: list[dict[str, Any]] = []
    if sink is not None and MODEL_CALLS_PLAIN.exists():
        model_log = [json.loads(l) for l in MODEL_CALLS_PLAIN.read_text(encoding="utf-8").splitlines() if l.strip()]
    harness.MODEL_LOG = model_log
    flushed = len(model_log)
    lock = threading.Lock()

    def record(row: dict[str, Any]) -> None:
        nonlocal flushed
        with lock:
            rows.append(row)
            if sink is not None:
                with sink.open("a", encoding="utf-8", newline="\n") as handle:
                    handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
                if len(model_log) > flushed:
                    with MODEL_CALLS_PLAIN.open("a", encoding="utf-8", newline="\n") as handle:
                        for entry in model_log[flushed:]:
                            handle.write(json.dumps(entry, ensure_ascii=False) + "\n")
                    flushed = len(model_log)
            result = row.get("result") or {}
            print(json.dumps({"unit": [row["declaration"], row["arm"], row["search"]],
                              "expansions": len(result.get("expansions", [])), "proof": bool(result.get("proof")),
                              "abandoned": row.get("abandoned")}), flush=True)

    units = [(t, a, s) for t in tasks for a in arms for s in SEARCHES
             if (t["module"], t["declaration"], a, s) not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(run_unit, t, a, s, budget) for t, a, s in units]
        for future in concurrent.futures.as_completed(futures):
            record(future.result())
    return rows


def replication(rows: list[dict[str, Any]], tasks: list[dict[str, Any]]) -> dict[str, Any]:
    """C1: the menu arm's first 24 expansions against search-v0.1."""
    committed = {(r["module"], r["declaration"]): r for r in v1_rows() if r.get("task")}
    compared, matched, mismatches = 0, 0, []
    for row in rows:
        if row["arm"] != "menu" or "result" not in row:
            continue
        old = committed[(row["module"], row["declaration"])][f"menu.{row['search']}"]
        keys = WHOLE_KEYS if row["search"] == "whole" else ANDOR_KEYS
        new_exp = [{k: e[k] for k in keys} for e in row["result"]["expansions"][:V1_BUDGET]]
        old_exp = [{k: e[k] for k in keys} for e in old["expansions"][:V1_BUDGET]]
        old_proof = old["proof"]
        new_proof = row["result"]["proof"] if len(row["result"]["expansions"]) <= V1_BUDGET else None
        compared += 1
        if new_exp == old_exp and new_proof == old_proof:
            matched += 1
        else:
            first = next((i for i, (a, b) in enumerate(zip(new_exp, old_exp)) if a != b), min(len(new_exp), len(old_exp)))
            mismatches.append({"declaration": row["declaration"], "search": row["search"], "firstDifference": first})
    return {"compared": compared, "matched": matched, "mismatches": mismatches}


def summarize(rows: list[dict[str, Any]], tasks: list[dict[str, Any]], arms: list[str]) -> dict[str, Any]:
    by_unit = {(r["declaration"], r["arm"], r["search"]): r for r in rows}
    out: dict[str, Any] = {"experiment": "search-v0.2", "preregistrationSha256": sha256_file(PREREG),
                           "amendmentsSha256": {p.name: sha256_file(p) for p in amendments()},
                           "tasks": len(tasks), "arms": {}}
    for arm in arms:
        units = {s: [by_unit.get((t["declaration"], arm, s)) for t in tasks] for s in SEARCHES}
        ran = {s: [u for u in units[s] if u is not None and "result" in u] for s in SEARCHES}
        entry: dict[str, Any] = {
            "constructed": sum(1 for u in units["whole"] if u is not None and u.get("constructed")),
            "abandoned": {s: sum(1 for u in units[s] if u is not None and u.get("abandoned")) for s in SEARCHES},
            "checkpoints": {}}
        for b in CHECKPOINTS:
            expansions = [e for u in ran["whole"] for e in u["result"]["expansions"][:b]]
            n = len(expansions)
            order = sum(1 for e in expansions if e["orderDuplicate"])
            goal = sum(1 for e in expansions if e["goalDuplicate"])
            proved = {s: sum(1 for u in ran[s] if u["result"]["proof"] and len(u["result"]["expansions"]) <= b)
                      for s in SEARCHES}
            entry["checkpoints"][str(b)] = {
                "wholeExpansions": n, "orderDuplicates": order, "orderFraction": order / n if n else None,
                "goalDuplicates": goal, "goalFraction": goal / n if n else None,
                "wholeProved": proved["whole"], "andorProved": proved["andor"],
                "andorExpansions": sum(min(b, len(u["result"]["expansions"])) for u in ran["andor"]),
                "andorEntangled": sum(u["result"].get("entangled", 0) for u in ran["andor"]) if b == BUDGET else None}
        entry["frontierExhausted"] = {s: sum(1 for u in ran[s] if not u["result"]["proof"]
                                             and len(u["result"]["expansions"]) < BUDGET) for s in SEARCHES}
        out["arms"][arm] = entry
    a = out["arms"]
    last, first = str(BUDGET), str(V1_BUDGET)

    def frac(arm: str, b: str, key: str) -> float | None:
        return a[arm]["checkpoints"][b][key]

    ran_arms = [arm for arm in arms if a[arm]["checkpoints"][last]["wholeExpansions"]]
    out["hypotheses"] = {
        "H17": {"supported": bool(ran_arms) and all(
            frac(arm, last, "goalFraction") is not None and frac(arm, first, "goalFraction") is not None
            and frac(arm, last, "goalFraction") >= GROWTH_FACTOR * frac(arm, first, "goalFraction")
            for arm in ran_arms)},
        "H18": {"supported": bool(ran_arms) and all(
            a[arm]["checkpoints"][last]["andorProved"] >= a[arm]["checkpoints"][last]["wholeProved"]
            for arm in ran_arms) and any(
            a[arm]["checkpoints"][last]["andorProved"] > a[arm]["checkpoints"][last]["wholeProved"]
            for arm in ran_arms)},
        "H19": {"supported": bool(ran_arms) and all(
            frac(arm, last, "orderFraction") is not None and frac(arm, last, "orderFraction") < ORDER_CEILING
            for arm in ran_arms)},
        "armsRun": ran_arms,
    }
    out["C1"] = replication(rows, tasks)
    out["resultsSha256"] = sha256_file(RESULTS)
    out["modelCallsSha256"] = sha256_file(MODEL_CALLS) if MODEL_CALLS.exists() else None
    return out


def write_report(summary: dict[str, Any]) -> None:
    lines = ["# Deeper tactic search (search v0.2)", "",
             "The searches of search-v0.1, unchanged, at 192 expansions on the tasks where v0.1's budget of 24",
             "ran out; definitions, tasks, and hypotheses are frozen in `preregistration.json` (SHA-256",
             "`" + summary["preregistrationSha256"] + "`).", "",
             f"Tasks: {summary['tasks']}.", "",
             "| Arm | Budget | Whole-state expansions | Order duplicates | Goal duplicates | Proved: whole | "
             "Proved: AND-OR |",
             "| --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for arm, entry in summary["arms"].items():
        for b, c in entry["checkpoints"].items():
            if not c["wholeExpansions"]:
                continue
            lines.append(f"| {arm} | {b} | {c['wholeExpansions']} | {c['orderDuplicates']} ({c['orderFraction']:.1%}) | "
                         f"{c['goalDuplicates']} ({c['goalFraction']:.1%}) | {c['wholeProved']} | {c['andorProved']} |")
    h = summary["hypotheses"]
    c1 = summary["C1"]
    lines += ["", "## Hypotheses", "",
              f"- H17 (goal-duplicate fraction at 192 at least {GROWTH_FACTOR:g} times that at 24, both arms): "
              f"supported: {h['H17']['supported']}.",
              f"- H18 (AND-OR proves at least as many at 192 in both arms, more in one): supported: {h['H18']['supported']}.",
              f"- H19 (order-duplicate fraction at 192 below {ORDER_CEILING:.0%}, both arms): "
              f"supported: {h['H19']['supported']}.", "",
              f"C1 (menu arm reproduces search-v0.1's first 24 expansions): {c1['matched']} of {c1['compared']} "
              "searches.", "",
              "## Interpretation boundary", "",
              "Breadth-first search with a weak proposer, on the tasks where v0.1's searches ran out of",
              "budget. The measures describe where such a search spends its work as the budget grows,",
              "not the best achievable prover."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--arms", default=",".join(ARMS))
    args = parser.parse_args()
    arms = [a for a in args.arms.split(",") if a]

    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        tasks = select_tasks()
        write_lf(TASKS, json.dumps(tasks, indent=1, ensure_ascii=False) + "\n")
        payload = registration_payload(tasks)
        payload["tasksSha256"] = sha256_file(TASKS)
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["tasksSha256"] != sha256_file(TASKS):
        raise SystemExit("tasks changed since registration")
    if prereg["tasks"]["v1ResultsSha256"] != sha256_file(v1.RESULTS):
        raise SystemExit("the search-v0.1 results changed since registration")
    expected = expected_implementation_hashes(prereg)
    for name in ("harness", "repl"):
        if expected[name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration or the last amendment")
    tasks = json.loads(TASKS.read_text(encoding="utf-8"))

    if args.run:
        if "model" in arms and not model_server_alive():
            raise SystemExit("the local model server is not running")
        rows = run_all(tasks, arms, BUDGET, args.workers, RESULTS)
        order = {(t["declaration"], a, s): i for i, (t, a, s) in
                 enumerate((t, a, s) for t in tasks for a in ARMS for s in SEARCHES)}
        rows.sort(key=lambda r: order[(r["declaration"], r["arm"], r["search"])])
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        if harness.MODEL_LOG:
            MODEL_CALLS.write_bytes(gzip.compress("".join(json.dumps(m, ensure_ascii=False) + "\n"
                                                          for m in harness.MODEL_LOG).encode("utf-8"), 9, mtime=0))
            if MODEL_CALLS_PLAIN.exists():
                MODEL_CALLS_PLAIN.unlink()
        summary = summarize(rows, tasks, [a for a in ARMS if a in arms])
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({"search-v0.2-run": summary["hypotheses"], "C1": summary["C1"]["matched"]}))
        return 0

    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["preregistrationSha256"] != sha256_file(PREREG) \
            or summary["amendmentsSha256"] != {p.name: sha256_file(p) for p in amendments()}:
        raise SystemExit("summary hashes do not match the committed files")
    recomputed = summarize(committed, tasks, [a for a in ARMS if a in summary["arms"]])
    for key in ("arms", "hypotheses", "C1"):
        if recomputed[key] != summary[key]:
            raise SystemExit(f"the committed summary does not follow from the committed results ({key})")
    first = next((r for r in committed if r["arm"] == "menu" and r["search"] == "whole" and "result" in r), None)
    if first is not None:
        task = next(t for t in tasks if t["declaration"] == first["declaration"])
        fresh = run_unit(task, "menu", "whole", CHECK_BUDGET)["result"]["expansions"]
        want = first["result"]["expansions"][:CHECK_BUDGET]
        if [{k: e[k] for k in WHOLE_KEYS} for e in fresh] != [{k: e[k] for k in WHOLE_KEYS} for e in want]:
            raise SystemExit(f"the first task's menu search differs on re-run: {fresh} vs {want}")
    print(f"search-v0.2-check-ok: units={len(committed)} rerun={'yes' if first else 'no'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
