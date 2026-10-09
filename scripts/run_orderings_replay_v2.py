#!/usr/bin/env python3
"""Orderings replay v0.2: every proof the replay can pose, with goals that share a metavariable detected.

  python scripts/run_orderings_replay_v2.py --register
  python scripts/run_orderings_replay_v2.py --run [--workers 4]
  python scripts/run_orderings_replay_v2.py --check-committed

orderings-replay-v0.1 replayed every ordering of 64 small proofs drawn from the library and the first Mathlib slice:
all 197 other orderings of the 41 proofs whose original order replayed are scripts. Its sample rule does not test
whether goals share a metavariable, and no goal of the replayed proofs showed one. This experiment takes every proof
of the library and of both Mathlib slices that the same mechanism can replay, now with 3 to 12 steps and the step
derivation as corrected after extraction-audit-v0.1, and records at every step of every replay whether a goal shows a
metavariable, in its target or in a hypothesis. A proof is *coupled* when some goal of its original replay shows one.
Every ordering is replayed as in v0.1: `rotate_left` brings the goal a step consumed in the original proof to the
front, then the step's own text runs; an ordering replays when every tactic succeeds, every step leaves exactly the
goals the graph says it creates, no goal is left, and the script re-verifies from the statement. A proof with more
than 120 orderings replays the original and 119 others drawn with a fixed seed.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import random
import re
import sys
import threading
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import count_linearizations as counter  # noqa: E402
import count_linearizations_v2 as counter2  # noqa: E402
import run_holdout as holdout  # noqa: E402
import run_linearizations as library  # noqa: E402
import run_mathlib_slice as slice_  # noqa: E402
import run_orderings_replay as v1  # noqa: E402
import search_harness as harness  # noqa: E402
from lean_repl import LeanRepl, ReplTimeout  # noqa: E402
from run_linearizations import find_lake, read_gz_lines, sha256_file, write_lf  # noqa: E402
from run_search import generated  # noqa: E402

ROOT = library.ROOT
EXPERIMENT = ROOT / "experiments" / "orderings-replay-v0.2"
PREREG = EXPERIMENT / "preregistration.json"
SAMPLE = EXPERIMENT / "sample.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {"counter": ROOT / "scripts" / "count_linearizations.py",
                   "counter2": ROOT / "scripts" / "count_linearizations_v2.py",
                   "harness": ROOT / "scripts" / "search_harness.py",
                   "repl": ROOT / "scripts" / "lean_repl.py",
                   "replayV1": ROOT / "scripts" / "run_orderings_replay.py",
                   "runner": Path(__file__).resolve()}
CORPORA = {
    "proofnet-ir": {"extraction": library.EXTRACTION, "source": ROOT / ".lake" / "packages" / "proofnet-ir"},
    "mathlib-slice": {"extraction": slice_.EXTRACTION, "source": ROOT / ".lake" / "packages" / "mathlib"},
    "mathlib-holdout": {"extraction": holdout.EXTRACTION, "source": ROOT / ".lake" / "packages" / "mathlib"},
}
MIN_STEPS, MAX_STEPS = 3, 12
MAX_ORDERINGS = 120
SEED = 20261009
THRESHOLD = 0.9
METAVARIABLE = re.compile(r"(^|[\s(\[,])\?[\w.]")

HYPOTHESES = {
    "H97": f"over the proofs whose original order replays and none of whose goals shows a metavariable, at least "
           f"{THRESHOLD:.0%} of the other orderings replay",
    "H98": f"over the coupled proofs whose original order replays, fewer than {THRESHOLD:.0%} of the other orderings "
           f"replay",
    "H99": "the share of the other orderings that replay is lower over the coupled proofs than over the others",
}
CHECKS = {
    "C37": "the original order replays for at least 80% of the proofs that can be stated",
}


def eligible(corpus: str) -> list[dict[str, Any]]:
    paths = CORPORA[corpus]
    out = []
    cache: dict[str, list[str]] = {}
    for record in read_gz_lines(paths["extraction"]):
        roots = [n for n in record["nodes"] if n["parent"] is None]
        if len(roots) != 1 or not roots[0]["kind"].endswith("byTactic") or generated(record["declaration"]):
            continue
        steps = counter2.derive_steps(record["nodes"])
        if not MIN_STEPS <= len(steps) <= MAX_STEPS:
            continue
        parents = counter.dependency_graph(steps)
        if not all(len(ps) <= 1 for ps in parents) or any(len(s["consumed"]) != 1 for s in steps):
            continue
        produced = [g for s in steps for g in s["produced"]]
        consumed = [s["consumed"][0] for s in steps]
        roots_consumed = [c for c in consumed if c not in produced]
        if len(roots_consumed) != 1 or sorted(set(produced)) != sorted(set(consumed) - set(roots_consumed)):
            continue
        count = counter.forest_linearizations(parents)
        if count < 2:
            continue
        path = paths["source"] / (record["module"].replace(".", "/") + ".lean")
        if record["module"] not in cache:
            cache[record["module"]] = path.read_text(encoding="utf-8").split("\n")
        if v1.step_texts(record, steps, cache[record["module"]]) is None:
            continue
        out.append({"corpus": corpus, "module": record["module"], "declaration": record["declaration"],
                    "source": path.relative_to(ROOT).as_posix(), "byLine": roots[0]["line"],
                    "steps": len(steps), "orderings": count})
    return sorted(out, key=lambda e: (e["module"], e["byLine"], e["declaration"]))


def draw_sample() -> tuple[list[dict[str, Any]], dict[str, int]]:
    sample, pools = [], {}
    for corpus in CORPORA:
        pool = eligible(corpus)
        pools[corpus] = len(pool)
        sample += pool
    return sample, pools


def registration_payload(sample: list[dict[str, Any]], pools: dict[str, int]) -> dict[str, Any]:
    return {
        "experiment": "orderings-replay-v0.2",
        "question": "whether the orderings of a goal-origin graph replay as Lean scripts over every proof the replay "
                    "can pose, and whether they replay when goals share a metavariable",
        "sample": {"rule": f"every proof of the library and of both Mathlib slices with one root `by` block, a name "
                           f"that is not generated, {MIN_STEPS} to {MAX_STEPS} steps under the corrected step "
                           "derivation (count_linearizations_v2), a forest graph whose steps each consume one goal, "
                           "at least 2 orderings, and steps that can be cut out of the source one line each (v0.1's "
                           "rule: every other line of the body blank, a comment, or a bullet; no step line with `<;>`, "
                           "`;`, a nested `by`, or a structural tactic)",
                   "pools": pools, "count": len(sample),
                   "libraryExtractionSha256": sha256_file(library.EXTRACTION),
                   "sliceExtractionSha256": sha256_file(slice_.EXTRACTION),
                   "holdoutExtractionSha256": sha256_file(holdout.EXTRACTION)},
        "procedure": ["a fresh REPL per proof; the theorem is stated as an `example` in its module's context, as in "
                      "v0.1 and the search experiments",
                      "the original order first, then every other ordering (if there are more than "
                      f"{MAX_ORDERINGS}, {MAX_ORDERINGS - 1} others drawn with seed {SEED}), replayed step by step as "
                      "in v0.1: `rotate_left k` brings the goal the step consumed in the original proof to the front, "
                      "then the step's tactic text runs",
                      "an ordering replays when every tactic succeeds, every step leaves exactly the number of goals "
                      "the graph says it creates, no goal is left, and the script re-verifies from the statement",
                      "after every step, each goal is searched for a metavariable (a `?` followed by a name, after a "
                      "space, bracket, comma, or the start of a line), in its target and in its hypotheses; a proof is "
                      "coupled when some goal of its original replay shows one",
                      "a proof whose original order does not replay is reported and excluded from the measures"],
        "measures": {"replayed": "the other orderings that replay, over all other orderings replayed, pooled over the "
                                 "proofs of a class (coupled, or not) whose original order replays",
                     "failures": "for each ordering that does not replay, the first failure (goal selection, tactic "
                                 "error, goal count, goal missing, goals left, or verification) and, for a tactic error, "
                                 "Lean's message"},
        "hypotheses": HYPOTHESES,
        "checks": CHECKS,
        "tests": "H97 and H98 are decided by the pooled shares as stated; H99 compares the pooled shares, and is "
                 "untested if no coupled proof has another ordering",
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "the procedure was exercised only outside the sample: on "
                                               "fixtures/Coupled.lean (check_coupled_orderings.py: its original order "
                                               "replays and its other ordering fails on decide), and the static pool "
                                               "sizes were counted at 3 to 8, 3 to 12, and 3 to 20 steps (125, 134 and "
                                               "137 proofs) before the range was fixed; no proof of the sample was "
                                               "replayed",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def shows_metavariable(goal: str) -> tuple[bool, bool]:
    """Whether a printed goal shows a metavariable in its target, and anywhere."""
    target = goal.split("⊢")[-1]
    return bool(METAVARIABLE.search(target)), bool(any(METAVARIABLE.search(line) for line in goal.splitlines()))


def replay_order(repl: LeanRepl, session: Any, task: Any, steps: list[dict[str, Any]], texts: list[str],
                 root_goal: str, order: list[int]) -> dict[str, Any]:
    """v0.1's replay_order, also recording metavariables in hypotheses and the message of a failing tactic."""
    labels = [root_goal]
    proof_state = task.proof_state
    script: list[str] = []
    in_target = anywhere = 0
    for position, index in enumerate(order):
        step = steps[index]
        goal = step["consumed"][0]
        if goal not in labels:
            return {"ok": False, "failure": "goal missing", "at": position}
        k = labels.index(goal)
        if k > 0:
            moved = repl.tactic(proof_state, f"rotate_left {k}")
            if moved is None:
                return {"ok": False, "failure": "goal selection", "at": position}
            proof_state = moved[1]
            labels = labels[k:] + labels[:k]
            script.append(f"rotate_left {k}")
        result = repl.tactic(proof_state, texts[index])
        if result is None:
            response = repl._exchange({"tactic": texts[index], "proofState": proof_state}, repl.timeout)
            message = " ".join([m.get("data", "") for m in response.get("messages", [])
                                if m.get("severity") == "error"] + [response.get("message", "")]).strip()
            return {"ok": False, "failure": "tactic error", "at": position, "message": message[:300]}
        goals, proof_state = result
        for g in goals:
            target, any_place = shows_metavariable(g)
            in_target += target
            anywhere += any_place
        if len(goals) != len(labels) - 1 + len(step["produced"]):
            return {"ok": False, "failure": "goal count", "at": position}
        labels = list(step["produced"]) + labels[1:]
        script.append(texts[index])
    if labels:
        return {"ok": False, "failure": "goals left", "at": len(order)}
    if not session.verify(task, script):
        return {"ok": False, "failure": "verification", "at": len(order)}
    return {"ok": True, "mvarGoals": in_target, "mvarAnywhere": anywhere}


def orders_for(parents: list[set[int]], declaration: str) -> list[list[int]]:
    orders = v1.linear_extensions(parents)
    original = list(range(len(parents)))
    others = [o for o in orders if o != original]
    if len(others) > MAX_ORDERINGS - 1:
        others = random.Random(f"{SEED}:{declaration}").sample(others, MAX_ORDERINGS - 1)
    return [original] + others


def replay_proof(entry: dict[str, Any]) -> dict[str, Any]:
    head = {k: entry[k] for k in ("corpus", "module", "declaration", "steps", "orderings")}
    record = next(r for r in read_gz_lines(CORPORA[entry["corpus"]]["extraction"])
                  if r["module"] == entry["module"] and r["declaration"] == entry["declaration"])
    steps = counter2.derive_steps(record["nodes"])
    parents = counter.dependency_graph(steps)
    lines = (ROOT / entry["source"]).read_text(encoding="utf-8").split("\n")
    texts = v1.step_texts(record, steps, lines)
    produced = {g for s in steps for g in s["produced"]}
    root_goal = next(s["consumed"][0] for s in steps if s["consumed"][0] not in produced)
    orders = orders_for(parents, entry["declaration"])
    repl = LeanRepl(find_lake(), imports=None)
    started = time.monotonic()
    try:
        session = harness.ModuleSession(repl, entry["module"], ROOT / entry["source"],
                                        [(entry["declaration"], entry["byLine"])])
        task = None
        for _, made in session.tasks_in_order():
            task = made
            break
        if task is None:
            return head | {"stated": False, "seconds": round(time.monotonic() - started, 1)}
        original = replay_order(repl, session, task, steps, texts, root_goal, orders[0])
        others = []
        if original["ok"]:
            others = [replay_order(repl, session, task, steps, texts, root_goal, o) | {"order": o}
                      for o in orders[1:]]
    except ReplTimeout:
        return head | {"stated": True, "abandoned": "repl timeout", "seconds": round(time.monotonic() - started, 1)}
    finally:
        repl.close()
    return head | {"stated": True, "replayed": len(orders), "original": original,
                   "coupled": bool(original.get("mvarAnywhere")), "others": others,
                   "seconds": round(time.monotonic() - started, 1)}


def run_all(sample: list[dict[str, Any]], workers: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    done: set[tuple[str, str]] = set()
    if RESULTS.exists():
        rows = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
        done = {(r["module"], r["declaration"]) for r in rows}
    lock = threading.Lock()

    def guarded(entry: dict[str, Any]) -> dict[str, Any]:
        try:
            return replay_proof(entry)
        except Exception as error:  # noqa: BLE001  an unexpected failure is recorded, never lost
            return {k: entry[k] for k in ("corpus", "module", "declaration", "steps", "orderings")} | \
                {"stated": None, "error": f"{type(error).__name__}: {error}"[:300]}

    todo = [e for e in sample if (e["module"], e["declaration"]) not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        for row in pool.map(guarded, todo):
            with lock:
                rows.append(row)
                with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                    handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
                others = row.get("others", [])
                print(json.dumps({"proof": row["declaration"], "original": (row.get("original") or {}).get("ok"),
                                  "replayed": sum(1 for o in others if o["ok"]), "of": len(others),
                                  "error": row.get("error")}), flush=True)
    return rows


def share(rows: list[dict[str, Any]]) -> dict[str, Any]:
    others = [o for r in rows for o in r["others"]]
    ok = sum(1 for o in others if o["ok"])
    failures: dict[str, int] = {}
    for o in others:
        if not o["ok"]:
            failures[o["failure"]] = failures.get(o["failure"], 0) + 1
    return {"proofs": len(rows), "proofsWithOthers": sum(1 for r in rows if r["others"]), "orderings": len(others),
            "replayed": ok, "fraction": ok / len(others) if others else None, "failures": failures,
            "proofsAllReplay": sum(1 for r in rows if r["others"] and all(o["ok"] for o in r["others"])),
            "proofsNoneReplay": sum(1 for r in rows if r["others"] and not any(o["ok"] for o in r["others"]))}


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    stated = [r for r in rows if r.get("stated")]
    replayable = [r for r in stated if (r.get("original") or {}).get("ok")]
    coupled = [r for r in replayable if r["coupled"]]
    plain = [r for r in replayable if not r["coupled"]]
    original_failures: dict[str, int] = {}
    for r in stated:
        if r.get("original") and not r["original"]["ok"]:
            original_failures[r["original"]["failure"]] = original_failures.get(r["original"]["failure"], 0) + 1
    by_corpus = {c: {"proofs": sum(1 for r in rows if r["corpus"] == c),
                     "stated": sum(1 for r in stated if r["corpus"] == c),
                     "originalReplays": sum(1 for r in replayable if r["corpus"] == c),
                     "coupled": sum(1 for r in coupled if r["corpus"] == c)} for c in CORPORA}
    s_plain, s_coupled = share(plain), share(coupled)
    c37 = len(replayable) / len(stated) if stated else None
    return {"experiment": "orderings-replay-v0.2", "preregistrationSha256": sha256_file(PREREG),
            "proofs": len(rows), "stated": len(stated), "errors": sum(1 for r in rows if r.get("error")),
            "abandoned": sum(1 for r in rows if r.get("abandoned")), "originalReplays": len(replayable),
            "originalFailures": original_failures, "coupledProofs": len(coupled),
            "coupledInTargetOnly": sum(1 for r in coupled if r["original"].get("mvarGoals")),
            "byCorpus": by_corpus, "uncoupled": s_plain, "coupled": s_coupled,
            "hypotheses": {
                "H97": {"fraction": s_plain["fraction"], "orderings": s_plain["orderings"],
                        "supported": None if not s_plain["orderings"] else s_plain["fraction"] >= THRESHOLD},
                "H98": {"fraction": s_coupled["fraction"], "orderings": s_coupled["orderings"],
                        "supported": None if not s_coupled["orderings"] else s_coupled["fraction"] < THRESHOLD},
                "H99": {"coupled": s_coupled["fraction"], "uncoupled": s_plain["fraction"],
                        "supported": None if not (s_coupled["orderings"] and s_plain["orderings"])
                        else s_coupled["fraction"] < s_plain["fraction"]}},
            "checks": {"C37": {"fraction": c37, "holds": c37 is not None and c37 >= 0.8}},
            "resultsSha256": sha256_file(RESULTS)}


def write_report(summary: dict[str, Any]) -> None:
    s = summary

    def pct(x: float | None) -> str:
        return "n/a" if x is None else f"{x:.1%}"

    lines = ["# Replaying the orderings of goal-origin graphs (orderings replay v0.2)", "",
             f"Proofs: {s['proofs']}; stated: {s['stated']}; original order replays: {s['originalReplays']} "
             f"(failures of the original: {s['originalFailures']}); coupled: {s['coupledProofs']}.", "",
             f"Uncoupled: {s['uncoupled']['replayed']} of {s['uncoupled']['orderings']} other orderings replay "
             f"({pct(s['uncoupled']['fraction'])}); failures {s['uncoupled']['failures']}.", "",
             f"Coupled: {s['coupled']['replayed']} of {s['coupled']['orderings']} other orderings replay "
             f"({pct(s['coupled']['fraction'])}); failures {s['coupled']['failures']}.", ""]
    for key, entry in s["hypotheses"].items():
        lines.append(f"- {key}: {HYPOTHESES[key]}: supported {entry['supported']}.")
    lines.append(f"- C37: {CHECKS['C37']}: {s['checks']['C37']['holds']}.")
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        sample, pools = draw_sample()
        write_lf(SAMPLE, json.dumps(sample, indent=1, ensure_ascii=False) + "\n")
        payload = registration_payload(sample, pools)
        payload["sampleSha256"] = sha256_file(SAMPLE)
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(sample)} proofs (pools {pools}): {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["sampleSha256"] != sha256_file(SAMPLE):
        raise SystemExit("the sample changed since registration")
    for name in ("counter", "counter2", "harness", "repl", "replayV1"):
        if prereg["implementationSha256"][name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration")
    sample = json.loads(SAMPLE.read_text(encoding="utf-8"))
    if args.run:
        rows = run_all(sample, args.workers)
        order = {(e["module"], e["declaration"]): i for i, e in enumerate(sample)}
        rows.sort(key=lambda r: order[(r["module"], r["declaration"])])
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        summary = summarize(rows)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({k: summary[k] for k in ("proofs", "originalReplays", "coupledProofs", "hypotheses")}))
        return 0
    if not RESULTS.exists():
        print("orderings-replay-v0.2: registered, no results yet")
        return 0
    rows = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    if summarize(rows) != json.loads(SUMMARY.read_text(encoding="utf-8")):
        raise SystemExit("the committed summary does not follow from the committed results")
    print(f"orderings-replay-v0.2-check-ok: proofs={len(rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
