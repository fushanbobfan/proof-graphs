#!/usr/bin/env python3
"""Exploratory, not registered: what separates goals that print alike but have different faithful keys?

  python scripts/explore_false_merges.py --units 6 --out FILE

Replays keys-v0.1's units with the most false merges (the printed-goal AND-OR search) and the most false drops
(the printed whole-state search), recording each state's printed goals and faithful serializations in full, and
writes every false merge and false drop with both serializations and the tokens where they first differ.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import goal_identity as gi  # noqa: E402
import recording_repl  # noqa: E402
import run_key_replay as kr  # noqa: E402

TOKEN = re.compile(r"\?\d+|#\d+|h\d+|[A-Za-z_][\w.'!?₀-₉]*(?:\.\{[^}]*\})?|\d+|\S")


class TextRecordingRepl(recording_repl.RecordingRepl):
    def summarize(self, proof_state: int, goals: list[str]) -> dict[str, Any]:
        entry = super().summarize(proof_state, goals)
        exported = gi.export(self, proof_state)
        entry["printed"] = goals
        entry["faithfulText"] = [gi._renumber([g])[0] for g in exported] if exported and len(exported) == len(goals) else None
        entry["stateText"] = gi._renumber(exported) if exported and len(exported) == len(goals) else None
        return entry


def first_difference(a: str, b: str) -> dict[str, Any]:
    ta, tb = TOKEN.findall(a), TOKEN.findall(b)
    # A linear scan: difflib's matcher is quadratic on the longest serializations and only the first
    # difference is reported.
    at = next((i for i, (x, y) in enumerate(zip(ta, tb)) if x != y), None if len(ta) == len(tb) else min(len(ta), len(tb)))
    if at is None:
        return {"at": None}
    return {"at": at, "context": " ".join(ta[max(0, at - 8):at]), "first": " ".join(ta[at:at + 12]),
            "second": " ".join(tb[at:at + 12])}


def merges(log: dict[str, Any]) -> list[dict[str, Any]]:
    states, out = log["states"], []
    steps = kr.expansions_of(log)
    root = states[str(steps[0][0])]
    nodes = {root["default"][0]: (root["faithful"][0] if root["faithful"] else None,
                                  root["faithfulText"][0] if root.get("faithfulText") else None)}
    for state, children in steps:
        carried = states[str(state)]["default"][1:]
        for child in children:
            c = states[str(child)]
            goals = c["default"]
            if len(goals) < len(carried) or (carried and goals[len(goals) - len(carried):] != carried):
                continue
            for i in range(len(goals) - len(carried)):
                key, faithful = goals[i], c["faithful"][i] if c["faithful"] else None
                text = c["faithfulText"][i] if c.get("faithfulText") else None
                if key in nodes:
                    known, known_text = nodes[key]
                    if known is not None and faithful is not None and known != faithful:
                        out.append({"printed": c["printed"][i], "first": known_text, "second": text,
                                    "difference": first_difference(known_text or "", text or "")})
                else:
                    nodes[key] = (faithful, text)
    return out


def drops(log: dict[str, Any], text_key: str) -> list[dict[str, Any]]:
    """Children a whole-state search drops as duplicates under its text key whose faithful state keys differ."""
    states, out = log["states"], []
    seen: dict[tuple[str, ...], tuple[str | None, list[str] | None]] = {}
    for state, children in kr.expansions_of(log):
        s = states[str(state)]
        seen.setdefault(tuple(s[text_key]), (s["state"], s.get("stateText")))
        for child in children:
            c = states[str(child)]
            key = tuple(c[text_key])
            if key in seen:
                known, known_text = seen[key]
                if known is not None and c["state"] is not None and known != c["state"]:
                    a, b = "\n\n".join(known_text or []), "\n\n".join(c.get("stateText") or [])
                    out.append({"printed": c["printed"], "difference": first_difference(a, b)})
            else:
                seen[key] = (c["state"], c.get("stateText"))
    return out


IDENT = re.compile(r"[A-Za-z_][\w.'!?₀-₉]*")
INSTANCE = re.compile(r"\.to[A-Z]|^inst|\.inst|Inst")


def category(difference: dict[str, Any]) -> str:
    """Where two conflated serializations first differ, by the first identifier on each side."""
    context = difference.get("context") or ""
    first, second = (difference.get("first") or "").split(), (difference.get("second") or "").split()
    if context.rfind("{") > context.rfind("}") or "max" in first[:1] + second[:1]:
        return "universe level"
    x = next((t for t in first if IDENT.fullmatch(t)), "")
    y = next((t for t in second if IDENT.fullmatch(t)), "")
    if re.fullmatch(r"h\d+", x) and re.fullmatch(r"h\d+", y):
        return "hypothesis reference"
    if "._proof_" in x + y or {x, y} & {"Eq.ndrec.", "Eq.mpr.", "Eq.mp."}:
        return "proof term"
    if "fun" in (first[:3] + second[:3]):
        return "lambda"
    if INSTANCE.search(x) or INSTANCE.search(y):
        return "instance path"
    return "other"


def summarize(full: Path, out: Path) -> dict[str, Any]:
    report = json.loads(full.read_text(encoding="utf-8"))
    items = [{"unit": u["unit"], "kind": u["kind"], "difference": f["difference"],
              "category": category(f["difference"])} for u in report for f in u.get("found", [])]
    counts: dict[str, dict[str, int]] = {}
    for item in items:
        counts.setdefault(item["kind"], {}).setdefault(item["category"], 0)
        counts[item["kind"]][item["category"]] += 1
    units = [{"unit": u["unit"], "kind": u["kind"], "found": len(u.get("found", [])),
              "recorded": u.get("recorded", {}).get("andor" if u["kind"] == "merges" else "whole", {})
              .get("falseMerges" if u["kind"] == "merges" else "falseDrops")} for u in report]
    summary = {"registered": False, "units": units, "counts": counts, "items": items}
    out.write_text(json.dumps(summary, indent=1, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--units", type=int, default=6)
    parser.add_argument("--out", required=True)
    parser.add_argument("--summarize", metavar="FULL_REPORT",
                        help="categorize a full report's first differences into --out instead of replaying")
    args = parser.parse_args()
    if args.summarize:
        summary = summarize(Path(args.summarize), Path(args.out))
        print(json.dumps(summary["counts"]))
        return 0
    rows = [json.loads(l) for l in kr.RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    ranked_merges = sorted((r for r in rows if r["search"] == "andor" and "audit" in r),
                           key=lambda r: -r["audit"]["andor"]["falseMerges"])[:args.units]
    ranked_drops = sorted((r for r in rows if r["search"] == "whole" and r["kind"] == "prover" and "audit" in r),
                          key=lambda r: -r["audit"]["whole"]["falseDrops"])[:args.units]
    tasks = {(t["module"], t["declaration"]): t for t in kr.v6.tasks()}
    sets = kr.recorded_draws()
    kr.RecordingRepl = TextRecordingRepl
    report = []
    for row, kind in [(r, "merges") for r in ranked_merges] + [(r, "drops") for r in ranked_drops]:
        task = tasks[(row["module"], row["declaration"])]
        replayed, log = kr.run_unit("prover", task, row["search"], sets.get(task["index"]))
        if log is None:
            report.append({"unit": row["unit"], "kind": kind, "replay": replayed})
            continue
        found = merges(log) if kind == "merges" else drops(log, "default")
        report.append({"unit": row["unit"], "kind": kind, "recorded": row["audit"], "outcome": replayed.get("outcome"),
                       "found": found})
        print(json.dumps({"unit": row["unit"][2][:50], "kind": kind, "found": len(found)}, ensure_ascii=False),
              flush=True)
    Path(args.out).write_text(json.dumps(report, indent=1, ensure_ascii=False), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
