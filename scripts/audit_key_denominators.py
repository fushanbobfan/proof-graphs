#!/usr/bin/env python3
"""Recompute keys-v0.1 denominators from committed data, without Lean or search imports.

  python scripts/audit_key_denominators.py
  python scripts/audit_key_denominators.py --check

The expression keys here are the recorded v1 keys, not typed v2 keys. Duplicate histories are rebuilt
per unit on the common support of exported expansions. False identifications retain the searches'
original text-key histories; missing expression comparisons are reported separately.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
SOURCE = "experiments/keys-v0.1"
OUTPUT = ROOT / "experiments" / "keys-v0.1-matched-support"
ARMS = {"proverWhole": ("prover", "whole"), "proverWholeRenamed": ("prover", "wholeRenamed"),
        "proverAndor": ("prover", "andor"), "proverAndorRenamed": ("prover", "andorRenamed"),
        "menuWhole": ("menu", "whole")}


def expansions_of(log: dict[str, Any]) -> list[tuple[int, list[int]]]:
    """Reconstruct expansion/candidate events, excluding a pick immediately followed by expansion."""
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
    if len(out) != len(log["expansions"]):
        raise ValueError("event/expansion count mismatch")
    return out


def matched_duplicates(log: dict[str, Any]) -> dict[str, int]:
    """Count both first-goal histories using only the same successfully exported expansions."""
    counts = {"total": 0, "evaluable": 0, "missing": 0, "expressionDuplicates": 0, "coarseDuplicates": 0}
    expression_seen: set[str] = set()
    coarse_seen: set[str] = set()
    for state, _ in expansions_of(log):
        counts["total"] += 1
        entry = log["states"][str(state)]
        expression, coarse = entry["faithful"], entry["coarse"]
        if expression is None or entry["state"] is None:
            counts["missing"] += 1
            continue
        if not expression or coarse is None or len(expression) != len(coarse):
            raise ValueError("exported expansion has missing or inconsistent goal keys")
        counts["evaluable"] += 1
        counts["expressionDuplicates"] += expression[0] in expression_seen
        counts["coarseDuplicates"] += coarse[0] in coarse_seen
        expression_seen.add(expression[0])
        coarse_seen.add(coarse[0])
    return counts


def _comparison(counts: dict[str, int], ours: str | None, theirs: str | None) -> None:
    counts["total"] += 1
    if ours is None or theirs is None:
        counts["missing"] += 1
    else:
        counts["evaluable"] += 1
        counts["false"] += ours != theirs


def false_drops(log: dict[str, Any], text_key: str) -> dict[str, int]:
    """Rebuild original whole-state drop decisions, including unexported states in text history."""
    counts = {"total": 0, "evaluable": 0, "missing": 0, "false": 0}
    steps = expansions_of(log)
    if not steps:
        return counts
    states = log["states"]
    root = states[str(steps[0][0])]
    seen = {tuple(root[text_key]): root["state"]}
    for (_, children), recorded in zip(steps, log["expansions"]):
        dropped = 0
        for child in children:
            entry = states[str(child)]
            if not entry[text_key]:
                continue
            key = tuple(entry[text_key])
            if key in seen:
                dropped += 1
                _comparison(counts, entry["state"], seen[key])
            else:
                seen[key] = entry["state"]
        expected = (recorded.get("exactDuplicates") or 0) + (recorded.get("renamedDuplicates") or 0)
        if dropped != expected:
            raise ValueError("reconstructed drops differ from recorded decisions")
    return counts


def false_merges(log: dict[str, Any]) -> dict[str, int]:
    """Rebuild printed AND-OR arrivals and merges, excluding entangled candidates and the root."""
    counts = {"total": 0, "evaluable": 0, "missing": 0, "false": 0}
    steps = expansions_of(log)
    if not steps:
        return counts
    states = log["states"]
    root = states[str(steps[0][0])]
    nodes = {root["default"][0]: root["faithful"][0] if root["faithful"] else None}
    for state, children in steps:
        carried = states[str(state)]["default"][1:]
        for child in children:
            entry = states[str(child)]
            goals = entry["default"]
            tail = goals[len(goals) - len(carried):] if carried else []
            if len(goals) < len(carried) or tail != carried:
                continue
            for i in range(len(goals) - len(carried)):
                key = goals[i]
                expression = entry["faithful"][i] if entry["faithful"] else None
                if key in nodes:
                    _comparison(counts, expression, nodes[key])
                else:
                    nodes[key] = expression
    return counts


def _share(numerator: int, denominator: int) -> float | None:
    return numerator / denominator if denominator else None


def _committed(path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"HEAD:{path}"], cwd=ROOT)


def content_sha256(name: str, data: bytes) -> str:
    """The repository's content hash (`run_linearizations.sha256_file`): a `.gz` file hashed decompressed, CRLF as LF."""
    raw = gzip.decompress(data) if name.endswith(".gz") else data
    return hashlib.sha256(raw.replace(b"\r\n", b"\n")).hexdigest()


def source_hash_checks(data: dict[str, bytes], old: dict[str, Any]) -> dict[str, Any]:
    """Report stale digest metadata without substituting another blob or discarding usable log records."""
    checks = {}
    for filename, hash_field in (("logs.jsonl.gz", "logsSha256"), ("results.jsonl", "resultsSha256")):
        actual = content_sha256(filename, data[filename])
        checks[filename] = {"expected": old[hash_field], "actual": actual, "matches": actual == old[hash_field]}
    return checks


def summarize() -> dict[str, Any]:
    data = {name: _committed(f"{SOURCE}/{name}") for name in ("logs.jsonl.gz", "results.jsonl", "summary.json")}
    old = json.loads(data["summary.json"])
    hash_checks = source_hash_checks(data, old)
    rows = [json.loads(line) for line in data["results.jsonl"].splitlines() if line.strip()]
    entries = [json.loads(line) for line in gzip.decompress(data["logs.jsonl.gz"]).splitlines() if line.strip()]
    logs = {tuple(entry["unit"]): entry["log"] for entry in entries}
    if len(logs) != len(entries) or len({tuple(row["unit"]) for row in rows}) != len(rows):
        raise ValueError("duplicate units in committed artifacts")
    if set(logs) != {tuple(row["unit"]) for row in rows if "audit" in row}:
        raise ValueError("logged units differ from audited result units")
    out: dict[str, Any] = {
        "analysis": "keys-v0.1-matched-support", "expressionKeyVersion": 1,
        "sourceSha256": {name: content_sha256(name, value) for name, value in data.items()},
        "sourceHashChecks": hash_checks,
        "scope": "Observed expansions in logged units; histories reset for each unit. Unlogged units' "
                 "expansions and decisions are unknown, not zero.",
        "limitations": [
            "Only v1 key digests are recorded; instantiated expression trees needed to recompute v2 keys "
            "and corrected unordered state identity are absent.",
            "Renamed AND-OR merge decisions, alias-to-node mappings, accepted renaming targets, and goal "
            "text for rebuilding renaming_step/agrees are absent. Its false-merge counts and share "
            "cannot be recovered; coarse-key equality alone is not an accepted merge.",
        ], "arms": {},
    }
    for name, (kind, search) in ARMS.items():
        members = [row for row in rows if row["kind"] == kind and row["search"] == search]
        dup = {"total": 0, "evaluable": 0, "missing": 0, "expressionDuplicates": 0, "coarseDuplicates": 0}
        comparisons = {"total": 0, "evaluable": 0, "missing": 0, "false": 0}
        logged = 0
        for row in members:
            log = logs.get(tuple(row["unit"]))
            if log is None:
                continue
            logged += 1
            counts = matched_duplicates(log)
            expected = row["audit"].get("whole", row["audit"].get("repeats"))
            if counts["total"] != expected["expansions"]:
                raise ValueError("expansion total differs from committed result")
            for key in dup:
                dup[key] += counts[key]
            if search in ("whole", "wholeRenamed"):
                counts = false_drops(log, "default" if search == "whole" else "coarse")
                before = row["audit"]["whole"]
                expected_counts = (before["dropped"], before["falseDrops"], before["undefined"])
            elif search == "andor":
                counts = false_merges(log)
                before = row["audit"]["andor"]
                expected_counts = (before["merged"], before["falseMerges"], before["undefined"])
            else:
                continue
            if (counts["total"], counts["false"], counts["missing"]) != expected_counts:
                raise ValueError("reconstructed false identification counts differ from committed result")
            for key in comparisons:
                comparisons[key] += counts[key]
        dup |= {"expressionShare": _share(dup["expressionDuplicates"], dup["evaluable"]),
                "coarseShare": _share(dup["coarseDuplicates"], dup["evaluable"])}
        entry: dict[str, Any] = {"units": len(members), "loggedUnits": logged,
                                 "unloggedUnits": len(members) - logged, "goalDuplicates": dup}
        if logged != old[name]["audited"]:
            raise ValueError("logged unit count differs from committed summary")
        measure = "falseDrops" if search in ("whole", "wholeRenamed") else "falseMerges"
        entry[measure] = ({"status": "unavailable", "total": None, "evaluable": None, "missing": None,
                           "false": None, "share": None, "reason": out["limitations"][1]}
                          if search == "andorRenamed" else
                          comparisons | {"status": "evaluable", "share": _share(comparisons["false"],
                                                                                   comparisons["evaluable"])})
        out["arms"][name] = entry
    drops = [entry["falseDrops"] for entry in out["arms"].values() if "falseDrops" in entry]
    total = {key: sum(entry[key] for entry in drops) for key in ("total", "evaluable", "missing", "false")}
    out["falseDropsPooled"] = total | {"share": _share(total["false"], total["evaluable"])}
    return out


def report(summary: dict[str, Any]) -> str:
    lines = ["# Keys v0.1: matched-support denominators", "",
             "Exploratory audit of committed v1 expression-key digests. No v2 keys are recomputed.", "",
             "Both goal-duplicate histories use only expansions whose state exported. Each history starts "
             "empty in each unit; only its first goal is counted. Shares divide by evaluable expansions.", "",
             "| Arm | Logged / total units | Expansion total | Evaluable | Missing | Expression duplicates / share "
             "| Coarse duplicates / share |", "| --- | ---: | ---: | ---: | ---: | ---: | ---: |"]

    def pct(value: float | None) -> str:
        return "unavailable" if value is None else f"{value:.4%}"

    for name, arm in summary["arms"].items():
        d = arm["goalDuplicates"]
        lines.append(f"| {name} | {arm['loggedUnits']} / {arm['units']} | {d['total']} | {d['evaluable']} | "
                     f"{d['missing']} | {d['expressionDuplicates']} / {pct(d['expressionShare'])} | "
                     f"{d['coarseDuplicates']} / {pct(d['coarseShare'])} |")
    lines += ["", "False identifications keep the original search's text-key history, including entries "
              "that did not export. A comparison is missing if either endpoint lacks an expression key. "
              "Shares divide by evaluable comparisons; missing comparisons are never counted as correct.", "",
              "| Arm / decision | Total | Evaluable | Missing | False | False / evaluable |",
              "| --- | ---: | ---: | ---: | ---: | ---: |"]
    for name, arm in summary["arms"].items():
        measure = "falseDrops" if "falseDrops" in arm else "falseMerges"
        d = arm[measure]
        if d["status"] == "unavailable":
            lines.append(f"| {name} / merges | unknown | unknown | unknown | unknown | unavailable |")
        else:
            lines.append(f"| {name} / {measure} | {d['total']} | {d['evaluable']} | {d['missing']} | "
                         f"{d['false']} | {pct(d['share'])} |")
    d = summary["falseDropsPooled"]
    lines += [f"| Pooled whole-state drops | {d['total']} | {d['evaluable']} | {d['missing']} | "
              f"{d['false']} | {pct(d['share'])} |", "", summary["scope"], "", "## Data limits", ""]
    lines += [f"- {limitation}" for limitation in summary["limitations"]]
    lines += ["", "Source SHA-256 digests are in summary.json; they cover logs.jsonl.gz, results.jsonl, "
              "and summary.json read with git show HEAD. The logs/results digests are checked against "
              "the source summary, with mismatches reported below. Reconstructed drops and printed AND-OR "
              "merges match committed per-unit "
              "counts. The root is excluded from printed AND-OR arrivals, as in the original audit.", "",
              "## Source integrity", ""]
    for name, check in summary["sourceHashChecks"].items():
        if check["matches"]:
            lines.append(f"- {name}: SHA-256 matches the source summary.")
        else:
            lines.append(f"- {name}: SHA-256 mismatch. Source summary records `{check['expected']}`; "
                         f"the committed blob is `{check['actual']}`. This audit uses the committed blob "
                         "and verifies gzip decoding, unit coverage, and per-unit decision counts. The "
                         "digest discrepancy's cause cannot be established from these three artifacts.")
    lines += ["", "```text", "python scripts/audit_key_denominators.py --check", "```", ""]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="compare the existing audit files without writing")
    args = parser.parse_args()
    summary = summarize()
    artifacts = {"summary.json": json.dumps(summary, indent=1, ensure_ascii=False) + "\n",
                 "README.md": report(summary)}
    if args.check:
        for name, text in artifacts.items():
            if (OUTPUT / name).read_bytes() != text.encode("utf-8"):
                raise SystemExit(f"audit artifact mismatch: {name}")
    else:
        if any((OUTPUT / name).exists() for name in artifacts):
            raise SystemExit("audit artifacts already exist; use --check")
        OUTPUT.mkdir(parents=True, exist_ok=True)
        for name, text in artifacts.items():
            with (OUTPUT / name).open("x", encoding="utf-8", newline="\n") as stream:
                stream.write(text)
    print("keys-v0.1-matched-support-ok: arms=5 loggedUnits="
          + str(sum(arm["loggedUnits"] for arm in summary["arms"].values())))
    for name, check in summary["sourceHashChecks"].items():
        if not check["matches"]:
            print(f"source hash mismatch: {name} expected={check['expected']} actual={check['actual']}")
    for name, arm in summary["arms"].items():
        d = arm["goalDuplicates"]
        decision = arm.get("falseDrops", arm.get("falseMerges"))
        print(f"{name}: expansions={d['total']} evaluable={d['evaluable']} missing={d['missing']} "
              f"expression={d['expressionDuplicates']} coarse={d['coarseDuplicates']} "
              f"false={decision['false']} decisionEvaluable={decision['evaluable']} "
              f"decisionMissing={decision['missing']} decisionTotal={decision['total']}")
    d = summary["falseDropsPooled"]
    print(f"pooled false drops: false={d['false']} evaluable={d['evaluable']} "
          f"missing={d['missing']} total={d['total']} share={d['share']:.8f}")
    print("renamed AND-OR false merges: unavailable (merge decisions and alias/target mappings not logged)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
