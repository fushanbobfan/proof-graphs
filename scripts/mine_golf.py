#!/usr/bin/env python3
"""Golf pairs from Mathlib's history: a proof and the proof that replaced it.

A *golf commit* is a first-parent commit of Mathlib between two tags whose
subject contains "golf" (case-insensitive): a pull request whose declared
purpose is to shorten or simplify proofs, merged after review. A *golf pair*
is a `theorem` or `lemma` that such a commit changed, where

- the statement (the text before the first `:=` outside brackets) is the
  same before and after, up to whitespace, and the proof is not;
- the after-text is still, verbatim, in the file at the upper tag, exactly
  once, so that the pair can be elaborated in one environment: the upper
  tag's file as it is, and the same file with the after-text replaced by the
  before-text.

Declarations are found by text: a line at column 0 starting with optional
modifiers and `theorem` or `lemma`, up to the next non-blank line at column
0. Declarations with the same name in one file are paired by occurrence
index, and skipped when the counts differ. No Lean runs here.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path
from typing import Any

DECLARATION = re.compile(r"(?:(?:private|protected|nonrec|noncomputable)\s+)*(?:theorem|lemma)\s+(\S+)")
OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄"}
CLOSE = {v: k for k, v in OPEN.items()}


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], capture_output=True, text=True, encoding="utf-8",
                          check=True).stdout


def git_show(repo: Path, rev: str, path: str) -> str | None:
    completed = subprocess.run(["git", "-C", str(repo), "show", f"{rev}:{path}"], capture_output=True, text=True,
                               encoding="utf-8")
    return completed.stdout if completed.returncode == 0 else None


def golf_commits(repo: Path, lower: str, upper: str) -> list[dict[str, str]]:
    out = []
    for line in git(repo, "log", "--first-parent", "--format=%H%x09%cs%x09%s", f"{lower}..{upper}").splitlines():
        sha, date, subject = line.split("\t", 2)
        if "golf" in subject.lower():
            out.append({"commit": sha, "date": date, "subject": subject})
    return out


def declaration_blocks(text: str) -> list[tuple[str, int, int, str]]:
    """(name, first line, end line exclusive, text) of every top-level theorem or lemma, 0-based lines."""
    lines = text.split("\n")
    out = []
    for start, line in enumerate(lines):
        match = DECLARATION.match(line)
        if not match:
            continue
        end = start + 1
        while end < len(lines) and (lines[end] == "" or lines[end][0] in " \t"):
            end += 1
        while end > start + 1 and lines[end - 1].strip() == "":
            end -= 1
        out.append((match.group(1), start, end, "\n".join(lines[start:end])))
    return out


def split_statement(block: str) -> tuple[str, str] | None:
    """The block split at its first `:=` outside brackets, or None."""
    depth: list[str] = []
    i = 0
    while i < len(block) - 1:
        ch = block[i]
        if block.startswith("--", i):  # line comment
            newline = block.find("\n", i)
            i = len(block) if newline == -1 else newline
            continue
        if block.startswith("/-", i):  # block comment
            close = block.find("-/", i + 2)
            i = len(block) if close == -1 else close + 2
            continue
        if ch in OPEN:
            depth.append(ch)
        elif ch in CLOSE and depth and depth[-1] == CLOSE[ch]:
            depth.pop()
        elif ch == ":" and block[i + 1] == "=" and not depth:
            return block[:i], block[i + 2:]
        i += 1
    return None


def normalize(text: str) -> str:
    return " ".join(text.split())


def pairs_of_commit(repo: Path, commit: dict[str, str], upper: str) -> tuple[list[dict[str, Any]], dict[str, int]]:
    sha = commit["commit"]
    stats = {"changedDeclarations": 0, "statementChanged": 0, "noSplit": 0, "changedSinceGolf": 0,
             "ambiguousName": 0, "whitespaceOnly": 0}
    pairs = []
    files = [f for f in git(repo, "diff", "--name-only", f"{sha}^", sha, "--", "Mathlib").splitlines()
             if f.endswith(".lean")]
    for path in files:
        before_text = git_show(repo, f"{sha}^", path)
        after_text = git_show(repo, sha, path)
        upper_text = git_show(repo, upper, path)
        if before_text is None or after_text is None:
            continue
        before_blocks: dict[str, list[tuple[int, int, str]]] = {}
        after_blocks: dict[str, list[tuple[int, int, str]]] = {}
        for name, s, e, t in declaration_blocks(before_text):
            before_blocks.setdefault(name, []).append((s, e, t))
        for name, s, e, t in declaration_blocks(after_text):
            after_blocks.setdefault(name, []).append((s, e, t))
        for name, afters in after_blocks.items():
            befores = before_blocks.get(name)
            if not befores:
                continue
            for index, (after_start, _, after_block) in enumerate(afters):
                if len(befores) != len(afters):
                    if any(b[2] != a[2] for b, a in zip(befores, afters)):
                        stats["ambiguousName"] += 1
                    break
                before_block = befores[index][2]
                if before_block == after_block:
                    continue
                stats["changedDeclarations"] += 1
                before_split, after_split = split_statement(before_block), split_statement(after_block)
                if before_split is None or after_split is None:
                    stats["noSplit"] += 1
                    continue
                if normalize(before_split[0]) != normalize(after_split[0]):
                    stats["statementChanged"] += 1
                    continue
                if normalize(before_split[1]) == normalize(after_split[1]):
                    stats["whitespaceOnly"] += 1
                    continue
                if upper_text is None or upper_text.count(after_block) != 1:
                    stats["changedSinceGolf"] += 1
                    continue
                upper_line = upper_text[:upper_text.index(after_block)].count("\n")
                module = ".".join(Path(path).with_suffix("").parts)
                pairs.append({"commit": sha, "date": commit["date"], "subject": commit["subject"],
                              "file": path, "module": module, "name": name, "occurrence": index,
                              "upperLine": upper_line + 1, "beforeLines": before_block.count("\n") + 1,
                              "afterLines": after_block.count("\n") + 1,
                              "before": before_block, "after": after_block})
    return pairs, stats


def mine(repo: Path, lower: str, upper: str) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    commits = golf_commits(repo, lower, upper)
    all_pairs: list[dict[str, Any]] = []
    totals: dict[str, int] = {}
    for commit in commits:
        pairs, stats = pairs_of_commit(repo, commit, upper)
        all_pairs += pairs
        for key, value in stats.items():
            totals[key] = totals.get(key, 0) + value
    # a declaration golfed twice in the window keeps only the golf whose after-text survives
    seen: dict[tuple[str, str, int], dict[str, Any]] = {}
    for pair in all_pairs:
        key = (pair["file"], pair["name"], pair["occurrence"])
        if key not in seen or pair["date"] > seen[key]["date"]:
            seen[key] = pair
    kept = sorted(seen.values(), key=lambda p: (p["module"], p["upperLine"]))
    totals["commits"] = len(commits)
    totals["commitsWithPairs"] = len({p["commit"] for p in kept})
    totals["pairs"] = len(kept)
    return kept, totals


if __name__ == "__main__":
    import json
    import sys

    repo, lower, upper = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
    pairs, totals = mine(repo, lower, upper)
    print(json.dumps(totals, indent=1))
