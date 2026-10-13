#!/usr/bin/env python3
"""Search cost v0.1: what each of the three searches spends, run alone and paying for its own draws.

  python scripts/run_search_cost.py --register
  python scripts/run_search_cost.py --run
  python scripts/run_search_cost.py --check-committed

The search comparisons count expansions, and search-v0.11 to v0.13 share each task's draws between its searches, so
whichever search reaches a goal first pays for its draw, and units run four at a time. Neither says what a search
costs. This experiment draws a seeded sample of search-v0.11's held-out tasks and runs search-v0.10's three searches
(whole states, independent goals, coupled groups; the typed key, 48 expansions) on each, one search at a time with
nothing else running, each in its own process and with its own fresh draws, and records the model's requests and
tokens and their time, the Lean candidate executions and their time, the exports that decide identity and their time,
the setup and verification commands, the peak memory of the search's processes, and the elapsed time.
"""

from __future__ import annotations

import argparse
import json
import os
import random
import statistics
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path
from typing import Any

import psutil

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_search_confirm as rc  # noqa: E402
import run_search_coupled as v8  # noqa: E402
import run_search_coupled_deep as deep  # noqa: E402
import run_search_goals_holdout as v12  # noqa: E402
import search_typed_v2 as guarded  # noqa: E402
import step_prover as prover  # noqa: E402
from run_linearizations import sha256_file, write_lf  # noqa: E402

ROOT = v8.ROOT
EXPERIMENT = ROOT / "experiments" / "search-cost-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
TASKS = EXPERIMENT / "tasks.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = dict(rc.IMPLEMENTATIONS) | {"confirmRunner": Path(rc.__file__).resolve(),
                                              "goalsRunner": Path(v12.__file__).resolve(),
                                              "runner": Path(__file__).resolve()}
SEARCHES = ("whole", "goals", "groups")
ORDERS = (("whole", "goals", "groups"), ("goals", "groups", "whole"), ("groups", "whole", "goals"))
SAMPLE = 30
BUDGET = 48
SEED = 20261015
POLL_SECONDS = 0.5
BOOTSTRAP = 2000
RATIO_BAND = (0.8, 1.25)
EXPORT_CEILING = 0.2

QUESTION = ("what each of the three searches costs on held-out tasks when it runs alone and pays for its own draws: "
            "model requests, tokens and time, Lean candidate executions, identity exports, memory, and elapsed time")
HYPOTHESES = {
    "H122": "in each search, the model's time is the largest of the recorded components of elapsed time (model draws, "
            "candidate tactics, exports, setup and verification commands) in more than half of the tasks",
    "H123": "the median over tasks of the group search's elapsed time divided by the whole-state search's lies between "
            "0.8 and 1.25",
    "H124": "in the independent-goal and group searches, the exports that decide identity take less than a fifth of the "
            "elapsed time in the median task",
}
CHECKS = {"C53": "every search of every sampled task runs to an outcome (a proof, an exhausted frontier, the budget, or "
                 "an abandoned session), and none raises",
          "C54": "no other search experiment's runner runs while a search of this one does"}
OTHER_RUNNERS = ("run_search_confirm.py", "run_search_goals_holdout.py", "run_search_replicates_holdout.py",
                 "run_search_typed.py", "run_search_coupled.py", "run_search_coupled_deep.py")


def sample_tasks() -> list[dict[str, Any]]:
    tasks = v12.held_out_tasks()
    chosen = sorted(random.Random(SEED).sample(range(len(tasks)), SAMPLE))
    return [tasks[i] for i in chosen]


# ---------------------------------------------------------------- one search in its own process


def run_search(task: dict[str, Any]) -> dict[str, Any]:
    """One search with fresh draws of its own; its draw log gives the model's requests, tokens, and time."""
    draws = v8.ReplicateDraws({})
    started = time.monotonic()
    row = guarded.run_one({k: v for k, v in task.items() if k not in ("search", "position")}, task["search"],
                          draws.proposer(task["search"]), BUDGET)
    elapsed = time.monotonic() - started
    model = {"requests": len(draws.log), "completions": len(draws.log) * v8.SAMPLES,
             "promptTokens": sum(e.get("promptTokens") or 0 for e in draws.log),
             "completionTokens": sum(e.get("completionTokens") or 0 for e in draws.log),
             "seconds": round(sum(e.get("seconds") or 0 for e in draws.log), 2)}
    return row | {"index": task["index"], "position": task["position"], "elapsedSeconds": round(elapsed, 2),
                  "model": model}


def other_runners() -> list[str]:
    found = []
    for p in psutil.process_iter(["cmdline"]):
        line = " ".join(p.info.get("cmdline") or [])
        if any(name in line for name in OTHER_RUNNERS):
            found.append(line[:120])
    return found


class PeakMemory:
    """The largest total resident memory of a process and its descendants, polled until stopped."""

    def __init__(self, pid: int) -> None:
        self.pid, self.peak, self._stop = pid, 0, threading.Event()
        self._thread = threading.Thread(target=self._poll, daemon=True)

    def _poll(self) -> None:
        while not self._stop.is_set():
            try:
                root = psutil.Process(self.pid)
                total = sum(p.memory_info().rss for p in [root, *root.children(recursive=True)])
                self.peak = max(self.peak, total)
            except psutil.Error:
                pass
            self._stop.wait(POLL_SECONDS)

    def __enter__(self) -> "PeakMemory":
        self._thread.start()
        return self

    def __exit__(self, *_: Any) -> None:
        self._stop.set()
        self._thread.join()


def search_in_child(task: dict[str, Any]) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as tmp:
        given, taken = Path(tmp) / "task.json", Path(tmp) / "row.json"
        given.write_text(json.dumps(task, ensure_ascii=False), encoding="utf-8")
        child = subprocess.Popen([sys.executable, "-B", str(Path(__file__).resolve()), "--search", str(given), str(taken)],
                                 cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
                                 encoding="utf-8", errors="replace",
                                 env=dict(os.environ, PYTHONUTF8="1", PYTHONIOENCODING="utf-8"),
                                 creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        with PeakMemory(child.pid) as memory:
            _, err = child.communicate()
        if child.returncode != 0 or not taken.exists():
            reason = (err.strip().splitlines() or [""])[-1]
            raise RuntimeError(f"search process exited with {child.returncode}: {reason[:200]}")
        row = json.loads(taken.read_text(encoding="utf-8"))
    return row | {"peakMemoryMB": round(memory.peak / 2**20, 1)}


def child_main(given: Path, taken: Path) -> int:
    prover.ENDPOINT = deep.ENDPOINT
    prover.MODEL_LOG = None
    row = run_search(json.loads(given.read_text(encoding="utf-8")))
    taken.write_text(json.dumps(row, ensure_ascii=False), encoding="utf-8")
    return 0


def read_rows() -> list[dict[str, Any]]:
    if not RESULTS.exists():
        return []
    return [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]


def run_all(tasks: list[dict[str, Any]]) -> None:
    if not deep.server_alive():
        raise SystemExit(f"the prover does not answer on port {deep.PORT}")
    done = {(r["declaration"], r["search"]) for r in read_rows() if not r.get("error")}
    for task in tasks:
        for position, search in enumerate(ORDERS[task["index"] % len(ORDERS)]):
            if (task["declaration"], search) in done:
                continue
            others = other_runners()
            try:
                row = search_in_child(task | {"search": search, "position": position})
            except Exception as error:  # noqa: BLE001
                row = {"module": task["module"], "declaration": task["declaration"], "search": search,
                       "index": task["index"], "position": position, "constructed": None,
                       "error": f"{type(error).__name__}: {error}"[:300]}
            row["othersRunning"] = others
            with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
            print(json.dumps({"task": task["declaration"][:40], "search": search,
                              "elapsed": row.get("elapsedSeconds"), "error": row.get("error"),
                              "at": time.strftime("%H:%M:%S")}), flush=True)


# ---------------------------------------------------------------- summary


def components(row: dict[str, Any]) -> dict[str, float]:
    costs = row.get("costs") or {}
    return {"model": row["model"]["seconds"], "tactic": (costs.get("tactic") or {}).get("seconds", 0.0),
            "export": (costs.get("export") or {}).get("seconds", 0.0),
            "command": (costs.get("command") or {}).get("seconds", 0.0)}


def median_interval(values: list[float], rng: random.Random) -> list[float] | None:
    if not values:
        return None
    meds = sorted(statistics.median(rng.choice(values) for _ in values) for _ in range(BOOTSTRAP))
    return [meds[int(0.025 * BOOTSTRAP)], meds[int(0.975 * BOOTSTRAP) - 1]]


def summarize(rows: list[dict[str, Any]], tasks: list[dict[str, Any]]) -> dict[str, Any]:
    latest = {(r["declaration"], r["search"]): r for r in rows}
    ran = {k: r for k, r in latest.items() if not r.get("error") and r.get("model")}
    per_search: dict[str, Any] = {}
    largest_model: dict[str, float] = {}
    for s in SEARCHES:
        mine = [r for (d, x), r in ran.items() if x == s]
        comps = [components(r) for r in mine]
        largest_model[s] = (sum(c["model"] == max(c.values()) for c in comps) / len(comps)) if comps else None
        per_search[s] = {
            "searches": len(mine), "proved": sum(bool((r.get("result") or {}).get("proof")) for r in mine),
            "abandoned": sum(bool(r.get("abandoned")) for r in mine),
            "medianElapsedSeconds": statistics.median(r["elapsedSeconds"] for r in mine) if mine else None,
            "medianPeakMemoryMB": statistics.median(r["peakMemoryMB"] for r in mine) if mine else None,
            "totals": {"elapsedSeconds": round(sum(r["elapsedSeconds"] for r in mine), 1),
                       "modelRequests": sum(r["model"]["requests"] for r in mine),
                       "completionTokens": sum(r["model"]["completionTokens"] for r in mine),
                       "promptTokens": sum(r["model"]["promptTokens"] for r in mine),
                       **{f"{k}Seconds": round(sum(c[k] for c in comps), 1) for k in ("model", "tactic", "export",
                                                                                     "command")},
                       "tacticCalls": sum(((r.get("costs") or {}).get("tactic") or {}).get("calls", 0) for r in mine),
                       "exportCalls": sum(((r.get("costs") or {}).get("export") or {}).get("calls", 0) for r in mine)},
            "modelLargestShareOfTasks": largest_model[s],
            "medianExportShare": statistics.median(c["export"] / r["elapsedSeconds"] for c, r in zip(comps, mine)
                                                   if r["elapsedSeconds"]) if mine else None,
        }
    rng = random.Random(SEED)
    ratios = {}
    for s in ("goals", "groups"):
        values = [ran[(t["declaration"], s)]["elapsedSeconds"] / ran[(t["declaration"], "whole")]["elapsedSeconds"]
                  for t in tasks if (t["declaration"], s) in ran and (t["declaration"], "whole") in ran
                  and ran[(t["declaration"], "whole")]["elapsedSeconds"]]
        ratios[f"{s}OverWhole"] = {"tasks": len(values), "median": statistics.median(values) if values else None,
                                   "interval95": median_interval(values, rng)}
    group_ratio = ratios["groupsOverWhole"]["median"]
    errors = [k for k, r in latest.items() if r.get("error")]
    contaminated = [k for k, r in latest.items() if r.get("othersRunning")]
    out = {"experiment": "search-cost-v0.1", "preregistrationSha256": sha256_file(PREREG), "tasks": len(tasks),
           "searches": per_search, "ratios": ratios}
    out["hypotheses"] = {
        "H122": {"shares": largest_model,
                 "holds": all(v is not None and v > 0.5 for v in largest_model.values())},
        "H123": {"median": group_ratio, "holds": group_ratio is not None
                 and RATIO_BAND[0] <= group_ratio <= RATIO_BAND[1]},
        "H124": {"shares": {s: per_search[s]["medianExportShare"] for s in ("goals", "groups")},
                 "holds": all(per_search[s]["medianExportShare"] is not None
                              and per_search[s]["medianExportShare"] < EXPORT_CEILING for s in ("goals", "groups"))},
    }
    out["checks"] = {"C53": {"expected": len(tasks) * len(SEARCHES), "ran": len(ran), "errors": len(errors),
                             "holds": len(ran) == len(tasks) * len(SEARCHES) and not errors},
                     "C54": {"contaminated": len(contaminated), "holds": not contaminated}}
    out["resultsSha256"] = sha256_file(RESULTS)
    return out


def write_report(s: dict[str, Any]) -> None:
    lines = ["# What each search costs, run alone with its own draws (search-cost v0.1)", "", f"Tasks: {s['tasks']}.", ""]
    for name, e in s["searches"].items():
        lines.append(f"- {name}: {json.dumps(e)}")
    lines += ["", f"Ratios: {json.dumps(s['ratios'])}", "", "## Hypotheses", ""]
    for key, e in s["hypotheses"].items():
        lines.append(f"- {key} ({'holds' if e['holds'] else 'fails'}): {HYPOTHESES[key]}.")
    lines += ["", "## Checks", ""]
    for key, e in s["checks"].items():
        lines.append(f"- {key} ({'holds' if e['holds'] else 'fails'}): {CHECKS[key]}.")
    write_lf(REPORT, "\n".join(lines) + "\n")


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "search-cost-v0.1", "question": QUESTION,
        "kind": "a cost characterization on a seeded sample of search-v0.11's held-out tasks, whose outcomes under "
                "shared draws were known (search-v0.11, v0.12) or being measured (search-v0.13) at registration",
        "tasks": {"rule": f"random.Random({SEED}).sample of {SAMPLE} of search-v0.11's tasks stated in both its "
                          "searches (search-v0.12's tasks), in their order", "count": len(tasks),
                  "tasksSha256": sha256_file(TASKS)},
        "searches": "search-v0.10's three searches (search_typed), the typed key, breadth-first, 48 expansions, each run "
                    "through search_typed_v2 in its own Python process and a fresh REPL",
        "draws": "each search draws its own candidates as search-v0.11 draws them, none shared with another search: the "
                 "nth time it expands a goal it receives the nth set it drew for that goal",
        "execution": "one search at a time, in an order that rotates with the task's index; run only after "
                     "search-v0.13 has finished, with no other search experiment's runner running (C54); the model "
                     f"server on port {deep.PORT} serves no one else",
        "measures": {"elapsed": "wall-clock time of the search, from its process's start of run_one to its end",
                     "model": "draw requests, 16 completions each, their prompt and generated tokens, and the time spent "
                              "drawing",
                     "lean": "candidate tactic calls, exports that decide identity, and setup and verification "
                             "commands, each with its time (the REPL's cost summary)",
                     "memory": f"the largest total resident memory of the search's process and its descendants, polled "
                               f"every {POLL_SECONDS} s"},
        "hypotheses": HYPOTHESES, "checks": CHECKS,
        "tests": "H122 to H124 decided by the rules as stated; medians are reported with percentile bootstrap intervals "
                 f"over tasks ({BOOTSTRAP} resamples), which do not decide",
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "none on these tasks: scripts/test_search_cost.py tests the accounting, "
                                               "the rotation, the memory poll and the summary without Lean",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def main() -> int:
    if sys.argv[1:2] == ["--search"]:
        return child_main(Path(sys.argv[2]), Path(sys.argv[3]))
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    for flag in ("--register", "--run", "--check-committed"):
        mode.add_argument(flag, action="store_true")
    args = parser.parse_args()
    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        tasks = sample_tasks()
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(TASKS, json.dumps(tasks, indent=1, ensure_ascii=False) + "\n")
        write_lf(PREREG, json.dumps(registration_payload(tasks), indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["tasks"]["tasksSha256"] != sha256_file(TASKS):
        raise SystemExit("the tasks changed since registration")
    for name, path in IMPLEMENTATIONS.items():
        if name != "runner" and prereg["implementationSha256"][name] != sha256_file(path):
            raise SystemExit(f"implementation {name} changed since registration")
    tasks = json.loads(TASKS.read_text(encoding="utf-8"))
    if args.run:
        if not (ROOT / "experiments" / "search-v0.13" / "summary.json").exists():
            raise SystemExit("search-v0.13 has not finished; this experiment runs alone")
        run_all(tasks)
        summary = summarize(read_rows(), tasks)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({k: {"holds": v["holds"]} for k, v in summary["hypotheses"].items()}))
        return 0
    if not RESULTS.exists():
        print("search-cost-v0.1: registered, no results yet")
        return 0
    if json.loads(SUMMARY.read_text(encoding="utf-8")) != json.loads(json.dumps(summarize(read_rows(), tasks))):
        raise SystemExit("the committed summary does not follow from the committed rows")
    print(f"search-cost-v0.1-check-ok: rows={len(read_rows())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
