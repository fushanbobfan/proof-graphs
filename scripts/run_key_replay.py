#!/usr/bin/env python3
"""Keys v0.1: finished searches replayed and re-keyed by Lean expressions.

  python scripts/run_key_replay.py --develop N
  python scripts/run_key_replay.py --register
  python scripts/run_key_replay.py --run [--workers 8]
  python scripts/run_key_replay.py --check-committed

Every duplicate share and every merge in search-v0.1 to v0.7 rests on text keys, which a review showed can merge
different goals and miss alike ones (experiments/goal-key-audit). This experiment replays two sets of finished
searches exactly, with the searches' code unchanged, and records every state they reach under the faithful key of
`goal_identity` (`recording_repl.RecordingRepl`):

- search-v0.7's four searches on its 200 tasks, from its recorded draws (search-v0.6's, which seeded it, and its
  own new ones), so that no model runs; a search that needs a draw not recorded has diverged, and raises;
- search-v0.4's keys arm, the menu's whole-state search on its 300 tasks, whose coarse-key share (28.0%) the
  audit could not check because no goal text was logged.

From the log it recomputes each search's own duplicate decisions under its text key, which must reproduce the
counts the search recorded, and then asks how the faithful key judges them: duplicate shares, states dropped and
goals merged as duplicates that the faithful key keeps apart, and states and goals kept apart that it identifies.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import gzip
import json
import random
import sys
import threading
import time
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common_draws  # noqa: E402
import run_search_keys as v4  # noqa: E402
import run_search_paired as v6  # noqa: E402
import run_search_renaming as v7  # noqa: E402
import search_harness as harness  # noqa: E402
import search_keys as keys  # noqa: E402
import search_renaming as renamed  # noqa: E402
import step_prover as prover  # noqa: E402
from lean_repl import ReplTimeout  # noqa: E402
from recording_repl import RecordingRepl  # noqa: E402
from run_linearizations import find_lake, sha256_file, write_lf  # noqa: E402
from search_harness import canonical_goal  # noqa: E402

ROOT = v7.ROOT
EXPERIMENT = ROOT / "experiments" / "keys-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
LOGS = EXPERIMENT / "logs.jsonl.gz"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "identity": ROOT / "scripts" / "goal_identity.py", "recorder": ROOT / "scripts" / "recording_repl.py",
    "keys": ROOT / "scripts" / "search_keys.py", "searchRenaming": ROOT / "scripts" / "search_renaming.py",
    "renaming": ROOT / "scripts" / "renaming.py", "harness": ROOT / "scripts" / "search_harness.py",
    "repl": ROOT / "scripts" / "lean_repl.py", "draws": ROOT / "scripts" / "common_draws.py",
    "runner": Path(__file__).resolve(),
}
FUNCTIONS: dict[str, Callable[..., dict[str, Any]]] = {
    "whole": keys.whole_state_search, "andor": keys.and_or_search,
    "wholeRenamed": renamed.whole_state_search, "andorRenamed": renamed.and_or_search}
PROVER_SEARCHES = ("whole", "andor", "wholeRenamed", "andorRenamed")
SHARE_MARGIN = 0.02
CEILING = 0.01


class ReplayDraws(common_draws.CommonDraws):
    """search-v0.7's draws of a task, complete; a search that needs another has left its recorded path."""

    def __init__(self, sets: dict[str, list[list[str]]]) -> None:
        super().__init__(v7.SAMPLES, v7.TEMPERATURE, v7.MAX_TOKENS, v7.MODEL_PATH)
        self.sets = {goal: [list(c) for c in s] for goal, s in sets.items()}

    def draw(self, goal: str) -> tuple[list[str], dict[str, Any]]:
        raise RuntimeError("the replay needed a draw that search-v0.7 did not make")


def recorded_draws() -> dict[int, dict[str, list[list[str]]]]:
    """search-v0.6's draws and search-v0.7's new ones, per task and goal, in occurrence order."""
    sets = v7.seeds_by_task()
    extra: dict[int, dict[str, dict[int, list[str]]]] = {}
    for entry in v7.read_draws():
        extra.setdefault(entry["index"], {}).setdefault(v7.draw_key(entry["prompt"]), {})[entry["occurrence"]] = \
            entry["candidates"]
    for index, goals in extra.items():
        for goal, by_occurrence in goals.items():
            have = sets.setdefault(index, {}).setdefault(goal, [])
            for n in sorted(by_occurrence):
                assert n == len(have), "search-v0.7's draws of a goal do not extend search-v0.6's"
                have.append(by_occurrence[n])
    return sets


def menu_tasks() -> list[dict[str, Any]]:
    return v4.draw_tasks()[:v4.KEY_TASKS]


def units() -> list[tuple[str, dict[str, Any], str]]:
    prover_units = [("prover", t, s) for t in v6.execution_order(v6.tasks()) for s in PROVER_SEARCHES]
    return prover_units + [("menu", t, "whole") for t in menu_tasks()]


def unit_key(kind: str, task: dict[str, Any], search: str) -> tuple[str, str, str, str]:
    return kind, task["module"], task["declaration"], search


def recorded_outcomes() -> dict[tuple[str, str, str, str], list[Any]]:
    out = {}
    for line in v7.RESULTS.read_text(encoding="utf-8").splitlines():
        row = json.loads(line)
        if "result" in row:
            out[("prover", row["module"], row["declaration"], row["search"])] = \
                [bool(row["result"]["proof"]), len(row["result"]["expansions"])]
    for line in v4.RESULTS.read_text(encoding="utf-8").splitlines():
        row = json.loads(line)
        if row.get("arm") == "keys" and "result" in row:
            out[("menu", row["module"], row["declaration"], "whole")] = \
                [bool(row["result"]["proof"]), len(row["result"]["expansions"])]
    return out


def run_unit(kind: str, task: dict[str, Any], search: str, sets: dict[str, list[list[str]]] | None,
             budget: int | None = None) -> tuple[dict[str, Any], dict[str, Any] | None]:
    head = {"kind": kind, "module": task["module"], "declaration": task["declaration"], "search": search}
    repl = RecordingRepl(find_lake(), imports=None)
    started = time.monotonic()
    try:
        path = ROOT / ".lake" / "packages" / "mathlib" / (task["module"].replace(".", "/") + ".lean")
        session = harness.ModuleSession(repl, task["module"], path, [(task["declaration"], task["line"])])
        for _, made in session.tasks_in_order():
            if made is None:
                return head | {"constructed": False}, None
            if kind == "prover":
                proposer = ReplayDraws(sets or {}).proposer(search)
                budget_ = v7.BUDGET if budget is None else budget
            else:
                proposer = keys.menu_proposer
                budget_ = v4.ARMS["keys"]["budget"] if budget is None else budget
            repl.recording = True
            result = FUNCTIONS[search](repl, made.proof_state, [made.goal], proposer, budget_,
                                       verifier=lambda script, m=made: session.verify(m, script))
            repl.recording = False
            log = {"expansions": [{k: e.get(k) for k in ("exactDuplicates", "renamedDuplicates", "goalDuplicate",
                                                         "orderDuplicate", "keys")} for e in result["expansions"]],
                   "events": repl.events, "states": {str(k): v for k, v in repl.states.items()}}
            return head | {"constructed": True, "outcome": [bool(result["proof"]), len(result["expansions"])],
                           "exportFailures": repl.export_failures, "states": len(repl.states),
                           "exportSeconds": round(repl.export_seconds, 1),
                           "seconds": round(time.monotonic() - started, 1)}, log
        return head | {"constructed": False, "reason": "declaration range not found"}, None
    except ReplTimeout:
        return head | {"constructed": True, "abandoned": "repl timeout",
                       "seconds": round(time.monotonic() - started, 1)}, None
    finally:
        repl.close()


# ---------------------------------------------------------------- reconstruction from a log


def expansions_of(log: dict[str, Any]) -> list[tuple[int, list[int]]]:
    """Each expanded state with its candidate results, in order. A `pick_goal n` whose result is expanded next is
    the harness bringing a goal to the front, not a candidate."""
    events = log["events"]
    out: list[tuple[int, list[int]]] = []
    for i, event in enumerate(events):
        if event[0] == "x":
            out.append((event[1], []))
        elif out and event[1] == out[-1][0]:
            following = events[i + 1] if i + 1 < len(events) else None
            if len(event) > 3 and following is not None and following[0] == "x" and following[1] == event[2]:
                continue
            out[-1][1].append(event[2])
    return out


def whole_state_audit(log: dict[str, Any], text_key: str) -> dict[str, Any]:
    """A whole-state search's own deduplication, recomputed under its text key (`default` for search_keys,
    `coarse` for search_renaming), and judged by the faithful state key."""
    states = log["states"]
    steps = expansions_of(log)
    counts = {"expansions": len(steps), "matchesRecorded": True, "children": 0, "dropped": 0, "falseDrops": 0,
              "kept": 0, "missedDrops": 0, "undefined": 0, "goalDuplicates": 0, "orderDuplicates": 0,
              "faithfulUndefined": 0}
    if len(steps) != len(log["expansions"]):
        counts["matchesRecorded"] = False
        return counts
    root = states[str(steps[0][0])]
    seen: dict[tuple[str, ...], str | None] = {tuple(root[text_key]): root["state"]}
    faithful_seen: set[str] = {root["state"]} if root["state"] else set()
    firsts: set[str] = set()
    multisets: dict[tuple[str, ...], set[tuple[str, ...]]] = {}
    for (state, children), recorded in zip(steps, log["expansions"]):
        entry = states[str(state)]
        if entry["faithful"] is None:
            counts["faithfulUndefined"] += 1
        else:
            ordered = tuple(entry["faithful"])
            multiset = tuple(sorted(ordered))
            counts["orderDuplicates"] += multiset in multisets and ordered not in multisets[multiset]
            counts["goalDuplicates"] += (ordered[0] if ordered else "") in firsts
            multisets.setdefault(multiset, set()).add(ordered)
            firsts.add(ordered[0] if ordered else "")
        dropped = 0
        for child in children:
            c = states[str(child)]
            if not c[text_key]:
                continue  # a closed state is not deduplicated
            counts["children"] += 1
            key = tuple(c[text_key])
            if key in seen:
                dropped += 1
                counts["dropped"] += 1
                if seen[key] is None or c["state"] is None:
                    counts["undefined"] += 1
                elif seen[key] != c["state"]:
                    counts["falseDrops"] += 1
            else:
                seen[key] = c["state"]
                counts["kept"] += 1
                if c["state"] is not None:
                    counts["missedDrops"] += c["state"] in faithful_seen
                    faithful_seen.add(c["state"])
        expected = (recorded.get("exactDuplicates") or 0) + (recorded.get("renamedDuplicates") or 0)
        counts["matchesRecorded"] &= dropped == expected
    return counts


def and_or_audit(log: dict[str, Any]) -> dict[str, Any]:
    """search_keys.and_or_search's merges by printed goal, recomputed, and judged by the faithful goal key."""
    states = log["states"]
    steps = expansions_of(log)
    counts = {"expansions": len(steps), "matchesRecorded": True, "arrivals": 0, "merged": 0, "falseMerges": 0,
              "new": 0, "missedMerges": 0, "undefined": 0, "entangled": 0}
    if len(steps) != len(log["expansions"]):
        counts["matchesRecorded"] = False
        return counts
    root = states[str(steps[0][0])]
    nodes: dict[str, str | None] = {root["default"][0]: root["faithful"][0] if root["faithful"] else None}
    faithful_nodes: set[str] = {root["faithful"][0]} if root["faithful"] else set()
    for state, children in steps:
        entry = states[str(state)]
        carried = entry["default"][1:]
        for child in children:
            c = states[str(child)]
            goals = c["default"]
            tail = goals[len(goals) - len(carried):] if carried else []
            if len(goals) < len(carried) or tail != carried:
                counts["entangled"] += 1
                continue
            for i in range(len(goals) - len(carried)):
                counts["arrivals"] += 1
                key = goals[i]
                faithful = c["faithful"][i] if c["faithful"] else None
                if key in nodes:
                    counts["merged"] += 1
                    if nodes[key] is None or faithful is None:
                        counts["undefined"] += 1
                    elif nodes[key] != faithful:
                        counts["falseMerges"] += 1
                else:
                    nodes[key] = faithful
                    counts["new"] += 1
                    if faithful is not None:
                        counts["missedMerges"] += faithful in faithful_nodes
                        faithful_nodes.add(faithful)
    counts["matchesRecorded"] &= all(states[str(s)]["default"][:1] == e["keys"]["default"][:1]
                                     for (s, _), e in zip(steps, log["expansions"]))
    return counts


def recorded_shares(log: dict[str, Any]) -> dict[str, int]:
    """The recorded goal and order duplicates of a whole-state search under its text keys."""
    out = {}
    for key in ("default", "coarse"):
        flags = [f for f in v4.flags([{"keys": e["keys"]} for e in log["expansions"]], key) if f is not None]
        out[f"{key}Goal"] = sum(1 for f in flags if f[1])
        out[f"{key}Order"] = sum(1 for f in flags if f[0])
    return out


def faithful_repeats(log: dict[str, Any]) -> dict[str, int]:
    """An AND-OR search's expansions of a goal whose faithful key an earlier expansion had."""
    seen: set[str] = set()
    repeats = undefined = 0
    for state, _ in expansions_of(log):
        faithful = log["states"][str(state)]["faithful"]
        if not faithful:
            undefined += 1
            continue
        repeats += faithful[0] in seen
        seen.add(faithful[0])
    return {"expansions": len(expansions_of(log)), "repeats": repeats, "undefined": undefined}


def unit_audit(row: dict[str, Any], log: dict[str, Any]) -> dict[str, Any]:
    search = row["search"]
    audit: dict[str, Any] = {"states": len(log["states"]),
                             "statesUndefined": sum(1 for v in log["states"].values() if v["faithful"] is None)}
    if search in ("whole", "wholeRenamed"):
        audit["whole"] = whole_state_audit(log, "default" if search == "whole" else "coarse")
        audit["recorded"] = recorded_shares(log)
    else:
        audit["repeats"] = faithful_repeats(log)
        if search == "andor":
            audit["andor"] = and_or_audit(log)
    return audit


# ---------------------------------------------------------------- running


def run_all(workers: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if RESULTS.exists():
        rows = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    logs = read_logs()
    done = {tuple(r["unit"]) for r in rows if not r.get("error")}
    sets = recorded_draws()
    lock = threading.Lock()
    prover.MODEL_LOG = None
    todo = [u for u in units() if unit_key(*u) not in done]

    def guarded(kind: str, task: dict[str, Any], search: str) -> tuple[dict[str, Any], dict[str, Any] | None]:
        started = time.monotonic()
        try:
            row, log = run_unit(kind, task, search, sets.get(task["index"]) if kind == "prover" else None)
            if log is not None:
                row["audit"] = unit_audit(row, log)
            return row, log
        except Exception as error:  # noqa: BLE001
            return {"kind": kind, "module": task["module"], "declaration": task["declaration"], "search": search,
                    "error": f"{type(error).__name__}: {error}"[:300],
                    "seconds": round(time.monotonic() - started, 1)}, None

    def record(unit: tuple[str, dict[str, Any], str], result: tuple[dict[str, Any], dict[str, Any] | None]) -> None:
        row, log = result
        row["unit"] = list(unit_key(*unit))
        with lock:
            rows.append(row)
            if log is not None:
                logs[json.dumps(row["unit"])] = log
            with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
            print(json.dumps({"unit": row["unit"][2][:40], "search": row["search"], "outcome": row.get("outcome"),
                              "error": row.get("error"), "at": time.strftime("%H:%M:%S")}, ensure_ascii=False),
                  flush=True)

    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(guarded, *u): u for u in todo}
        for future in concurrent.futures.as_completed(futures):
            record(futures[future], future.result())
    write_logs(logs)
    latest = {tuple(r["unit"]): r for r in rows}
    return list(latest.values())


def read_logs() -> dict[str, Any]:
    if not LOGS.exists():
        return {}
    out = {}
    for line in gzip.decompress(LOGS.read_bytes()).decode("utf-8").splitlines():
        if line.strip():
            entry = json.loads(line)
            out[json.dumps(entry["unit"])] = entry["log"]
    return out


def write_logs(logs: dict[str, Any]) -> None:
    lines = "".join(json.dumps({"unit": json.loads(k), "log": logs[k]}, separators=(",", ":")) + "\n"
                    for k in sorted(logs))
    LOGS.write_bytes(gzip.compress(lines.encode("utf-8"), compresslevel=9, mtime=0))


# ---------------------------------------------------------------- summary


def share(a: int, b: int) -> float | None:
    return None if b == 0 else a / b


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    recorded = recorded_outcomes()
    by_unit = {tuple(r["unit"]): r for r in rows}
    groups = {"proverWhole": ("prover", "whole"), "proverWholeRenamed": ("prover", "wholeRenamed"),
              "proverAndor": ("prover", "andor"), "proverAndorRenamed": ("prover", "andorRenamed"),
              "menuWhole": ("menu", "whole")}
    out: dict[str, Any] = {"experiment": "keys-v0.1", "preregistrationSha256": sha256_file(PREREG)}
    for name, (kind, search) in groups.items():
        members = [r for (k, _, _, s), r in by_unit.items() if k == kind and s == search]
        audited = [r["audit"] for r in members if "audit" in r]
        entry: dict[str, Any] = {"units": len(members), "audited": len(audited),
                                 "errors": sum(1 for r in members if r.get("error")),
                                 "abandoned": sum(1 for r in members if r.get("abandoned"))}
        if search in ("whole", "wholeRenamed"):
            total = {k: sum(a["whole"][k] for a in audited) for k in
                     ("expansions", "children", "dropped", "falseDrops", "kept", "missedDrops", "undefined",
                      "goalDuplicates", "orderDuplicates", "faithfulUndefined")}
            rec = {k: sum(a["recorded"][k] for a in audited) for k in
                   ("defaultGoal", "defaultOrder", "coarseGoal", "coarseOrder")}
            n = total["expansions"]
            entry |= {"totals": total, "recorded": rec,
                      "shares": {"faithfulGoal": share(total["goalDuplicates"], n),
                                 "faithfulOrder": share(total["orderDuplicates"], n),
                                 "defaultGoal": share(rec["defaultGoal"], n), "coarseGoal": share(rec["coarseGoal"], n),
                                 "defaultOrder": share(rec["defaultOrder"], n),
                                 "falseDrops": share(total["falseDrops"], total["dropped"]),
                                 "missedDrops": share(total["missedDrops"], total["kept"])},
                      "reconstructionMatches": sum(1 for a in audited if a["whole"]["matchesRecorded"])}
        else:
            reps = {k: sum(a["repeats"][k] for a in audited) for k in ("expansions", "repeats", "undefined")}
            entry |= {"repeats": reps, "repeatShare": share(reps["repeats"], reps["expansions"])}
            if search == "andor":
                total = {k: sum(a["andor"][k] for a in audited) for k in
                         ("arrivals", "merged", "falseMerges", "new", "missedMerges", "undefined", "entangled")}
                entry |= {"merges": total, "falseMergeShare": share(total["falseMerges"], total["merged"]),
                          "missedMergeShare": share(total["missedMerges"], total["new"]),
                          "reconstructionMatches": sum(1 for a in audited if a["andor"]["matchesRecorded"])}
        out[name] = entry
    compared = differing = 0
    differences = []
    for unit, row in by_unit.items():
        before = recorded.get(unit)
        now = row.get("outcome")
        if before is None and now is None:
            continue
        compared += 1
        if before != now:
            differing += 1
            differences.append({"unit": list(unit), "now": now, "before": before})
    states = sum(r["audit"]["states"] for r in rows if "audit" in r)
    undefined = sum(r["audit"]["statesUndefined"] for r in rows if "audit" in r)
    audited_units = [r for r in rows if "audit" in r]
    matching = sum(out[g].get("reconstructionMatches", 0) for g in ("proverWhole", "proverWholeRenamed",
                                                                    "proverAndor", "menuWhole"))
    reconstructable = sum(out[g]["audited"] for g in ("proverWhole", "proverWholeRenamed", "proverAndor", "menuWhole"))
    out["C10"] = {"compared": compared, "differing": differing, "differences": differences[:20],
                  "holds": compared > 0 and differing == 0}
    out["C11"] = {"reconstructable": reconstructable, "matching": matching, "holds": matching == reconstructable}
    out["C12"] = {"states": states, "undefined": undefined, "holds": states > 0 and undefined <= CEILING * states}
    pw, mw, pa = out["proverWhole"]["shares"], out["menuWhole"]["shares"], out["proverAndor"]
    drops = sum(out[g]["totals"]["dropped"] for g in ("proverWhole", "proverWholeRenamed", "menuWhole"))
    false_drops = sum(out[g]["totals"]["falseDrops"] for g in ("proverWhole", "proverWholeRenamed", "menuWhole"))

    def within(a: float | None, b: float | None) -> bool:
        return a is not None and b is not None and abs(a - b) <= SHARE_MARGIN

    out["hypotheses"] = {
        "H59": {"supported": within(pw["faithfulGoal"], pw["coarseGoal"])},
        "H60": {"supported": within(mw["faithfulGoal"], mw["coarseGoal"])},
        "H61": {"supported": pw["faithfulOrder"] is not None and pw["faithfulOrder"] < CEILING},
        "H62": {"supported": pa.get("falseMergeShare") is not None and pa["falseMergeShare"] < CEILING},
        "H63": {"supported": drops > 0 and false_drops / drops < CEILING}}
    out["drops"] = {"dropped": drops, "falseDrops": false_drops}
    out["auditedUnits"] = len(audited_units)
    out["resultsSha256"] = sha256_file(RESULTS)
    out["logsSha256"] = sha256_file(LOGS) if LOGS.exists() else None
    return out


def pct(x: float | None) -> str:
    return "n/a" if x is None else f"{100 * x:.1f}%"


def write_report(s: dict[str, Any]) -> None:
    lines = ["# Finished searches re-keyed by Lean expressions (keys v0.1)", "",
             "Frozen in `preregistration.json` (SHA-256 `" + s["preregistrationSha256"] + "`).", "",
             "| Whole-state search | Expansions | Goal dup. (default / coarse / faithful) | Order dup. (default / "
             "faithful) | Drops, false | Kept, faithfully duplicate |", "| --- | ---: | --- | --- | ---: | ---: |"]
    for name in ("proverWhole", "proverWholeRenamed", "menuWhole"):
        e = s[name]
        t, sh = e["totals"], e["shares"]
        lines.append(f"| {name} | {t['expansions']} | {pct(sh['defaultGoal'])} / {pct(sh['coarseGoal'])} / "
                     f"{pct(sh['faithfulGoal'])} | {pct(sh['defaultOrder'])} / {pct(sh['faithfulOrder'])} | "
                     f"{t['dropped']}, {t['falseDrops']} | {t['kept']}, {t['missedDrops']} |")
    a = s["proverAndor"]
    lines += ["", f"AND-OR search (printed goals): {a['merges']['arrivals']} goals created; {a['merges']['merged']} "
                  f"merged by print, {a['merges']['falseMerges']} of them with a different faithful key; "
                  f"{a['merges']['new']} new, {a['merges']['missedMerges']} of them faithfully equal to an "
                  f"existing goal. Expansions of a goal already expanded under the faithful key: "
                  f"{a['repeats']['repeats']} of {a['repeats']['expansions']} ({pct(a['repeatShare'])}); "
                  f"AND-OR up to renaming: {s['proverAndorRenamed']['repeats']['repeats']} of "
                  f"{s['proverAndorRenamed']['repeats']['expansions']} ({pct(s['proverAndorRenamed']['repeatShare'])}).",
              "", f"C10 (replays reproduce their outcomes): {s['C10']['compared']} compared, "
                  f"{s['C10']['differing']} differing. C11 (reconstruction reproduces the searches' own counts): "
                  f"{s['C11']['matching']} of {s['C11']['reconstructable']}. C12 (states exported): "
                  f"{s['C12']['states'] - s['C12']['undefined']} of {s['C12']['states']}.", "", "## Hypotheses", ""]
    lines += [f"- {k}: supported: {v['supported']}." for k, v in s["hypotheses"].items()]
    write_lf(REPORT, "\n".join(lines) + "\n")


# ---------------------------------------------------------------- registration and entry points


def registration_payload() -> dict[str, Any]:
    all_units = units()
    return {
        "experiment": "keys-v0.1",
        "question": "how do the searches' text keys compare with goal identity taken from Lean's expressions, on the "
                    "searches that produced the program's duplicate shares",
        "units": {"prover": "search-v0.7's four searches on its 200 tasks, replayed from its recorded draws "
                            "(search-v0.6's and its own new ones); a search that needs another draw raises",
                  "menu": "search-v0.4's keys arm: the menu's whole-state search at 24 expansions on its 300 tasks",
                  "count": len(all_units),
                  "sources": {"searchV07Results": sha256_file(v7.RESULTS), "searchV07Draws": sha256_file(v7.DRAWS),
                              "searchV06Draws": sha256_file(v7.SEED_DRAWS), "searchV04Results": sha256_file(v4.RESULTS),
                              "searchV04Tasks": sha256_file(v4.TASKS)}},
        "identity": "goal_identity.py: each goal's instantiated context and target exported by a run_tac block and "
                    "serialized structurally, hypotheses by position, bound variables by de Bruijn index, every "
                    "implicit argument and universe written, metavariables numbered by first occurrence with the "
                    "goals' own first; a state's faithful key is its goals' joint serialization in order",
        "recording": "recording_repl.py: the searches run unchanged in a REPL session that logs each expanded state "
                     "and each successful tactic, and exports every state reached",
        "measures": {
            "faithfulGoal/faithfulOrder": "a whole-state search's goal- and order-duplicate shares with the faithful "
                                          "goal key in place of the text key, over the same expansions",
            "drops": "child states a whole-state search dropped as duplicates under its text key (printed for "
                     "search_keys, coarse for search_renaming), recomputed from the log; false drops are those whose "
                     "faithful state key differs from that of the state they duplicate",
            "missedDrops": "child states kept whose faithful state key equals that of a state kept earlier",
            "merges": "the printed-goal AND-OR search's arrivals merged into an existing goal, recomputed; false "
                      "merges are those whose faithful goal key differs from the goal's; missed merges are new goals "
                      "whose faithful key an existing goal has",
            "repeats": "AND-OR expansions of a goal whose faithful key an earlier expansion had"},
        "hypotheses": {
            "H59": f"search-v0.7's whole-state search: the faithful goal-duplicate share is within "
                   f"{100 * SHARE_MARGIN:g} points of the coarse key's",
            "H60": f"search-v0.4's keys arm: the faithful goal-duplicate share is within {100 * SHARE_MARGIN:g} "
                   f"points of the coarse key's",
            "H61": f"search-v0.7's whole-state search: the faithful order-duplicate share is below {CEILING:.0%}",
            "H62": f"search-v0.7's printed-goal AND-OR search: fewer than {CEILING:.0%} of its merges join goals "
                   f"whose faithful keys differ",
            "H63": f"the whole-state searches (search-v0.7's two and search-v0.4's keys arm): fewer than "
                   f"{CEILING:.0%} of the states they drop as duplicates have a faithful key different from the state "
                   f"they duplicate"},
        "checks": {"C10": "every replayed unit reaches its recorded outcome (proved or not, at the same expansion)",
                   "C11": "on every unit, the duplicate decisions recomputed from the log reproduce the search's "
                          "recorded counts (whole-state: drops per expansion; AND-OR: the expanded goals)",
                   "C12": f"at most {CEILING:.0%} of the recorded states fail to export"},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": [
            "scripts/check_goal_identity.py: 8 cases in a Mathlib REPL, the review's two counterexamples among them",
            "--develop 2 --budget 8: the four search functions with the menu on two theorems of the first slice "
            "outside both corpora (Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson and wittPolynomial_vars, "
            "drawn with seed 11): every state of the 8 units exported (27 to 45 per unit), and the drops and merges "
            "recomputed from the logs matched the searches' own counts",
            "the draw replay of one search-v0.7 renaming search (MvPolynomial.mk_eq_eval₂, whole-state) with a plain "
            "REPL, computing no faithful key: from the merged draws (7,731 sets) it reached its recorded outcome "
            "(proved at expansion 14) without a new draw"],
        "resultsSeenBeforeRegistration": "every earlier experiment, including the outcomes the replays repeat and the "
                                         "text-key shares they re-key; the goal-key audit of the logged goals; no "
                                         "faithful key had been computed on a corpus task",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def develop(count: int, budget: int) -> int:
    """All four search functions with the menu, on tasks of the first slice outside both corpora."""
    menu = {t["declaration"] for t in menu_tasks()}
    corpus = {t["declaration"] for t in v6.tasks()} | menu
    source = ROOT / "experiments" / "search-v0.3" / "tasks.json"
    candidates = [t for t in json.loads(source.read_text(encoding="utf-8")) if t["declaration"] not in corpus]
    for task in random.Random(11).sample(candidates, count):
        for search in PROVER_SEARCHES:
            row, log = run_unit("menu", task, search, None, budget)
            audit = unit_audit(row, log) if log is not None else None
            size = len(json.dumps(log, separators=(",", ":"))) if log is not None else 0
            print(json.dumps({"task": task["declaration"][:40], "search": search, "outcome": row.get("outcome"),
                              "exportFailures": row.get("exportFailures"), "states": row.get("states"),
                              "seconds": row.get("seconds"), "logBytes": size, "audit": audit}, ensure_ascii=False),
                  flush=True)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--develop", type=int, metavar="N")
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--budget", type=int, default=8, help="with --develop")
    args = parser.parse_args()
    if args.develop:
        return develop(args.develop, args.budget)
    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(PREREG, json.dumps(registration_payload(), indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered: {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    for name in ("identity", "recorder", "keys", "searchRenaming", "renaming", "harness", "repl", "draws"):
        if prereg["implementationSha256"][name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration")
    if args.run:
        rows = run_all(args.workers)
        order = {unit_key(*u): i for i, u in enumerate(units())}
        rows.sort(key=lambda r: order.get(tuple(r["unit"]), len(order)))
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        summary = summarize(rows)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({"keys-v0.1-run": summary["hypotheses"], "C10": summary["C10"]["holds"],
                          "C11": summary["C11"]["holds"], "C12": summary["C12"]["holds"]}))
        return 0
    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["logsSha256"] != sha256_file(LOGS) \
            or summary["preregistrationSha256"] != sha256_file(PREREG):
        raise SystemExit("summary hashes do not match the committed files")
    logs = read_logs()
    for row in committed:
        key = json.dumps(row["unit"])
        if "audit" in row and row["audit"] != unit_audit(row, logs[key]):
            raise SystemExit(f"the committed audit of {row['unit']} does not follow from its log")
    recomputed = summarize(committed)
    for key in ("proverWhole", "proverWholeRenamed", "proverAndor", "proverAndorRenamed", "menuWhole", "C10", "C11",
                "C12", "hypotheses"):
        if recomputed[key] != summary[key]:
            raise SystemExit(f"the committed summary does not follow from the committed results ({key})")
    print(f"keys-v0.1-check-ok: units={len(committed)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

