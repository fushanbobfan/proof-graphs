#!/usr/bin/env python3
"""The step-dependency graphs of every extracted proof, as one dataset.

  python scripts/export_graphs.py          # write datasets/proof-graphs-v0.1.jsonl.gz
  python scripts/export_graphs.py --check  # recompute and compare with the committed file

One JSON line per proof, from the committed extractions of three
experiments: every tactic proof of ProofNet-IR v0.10.0
(`linearizations-v0.1`), of the Mathlib v4.32.0 slice
(`linearizations-mathlib-v0.1`), and both sides of every golf pair that
elaborated (`golf-v0.1`). The graph is the one the counter derives
(`scripts/count_linearizations.py`): `steps[i]` is the i-th step in
elaboration order with its tactic's syntax kind and source line, and an
edge `[p, i]` says that step i consumes a goal step p originated. Goal names
are omitted; they are fresh per elaboration and carry no meaning outside it.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import count_linearizations as counter  # noqa: E402
from run_linearizations import read_gz_lines  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "datasets" / "proof-graphs-v0.1.jsonl.gz"
SOURCES = [
    ("proofnet-ir@v0.10.0", ROOT / "experiments" / "linearizations-v0.1" / "extraction.jsonl.gz"),
    ("mathlib@v4.32.0", ROOT / "experiments" / "linearizations-mathlib-v0.1" / "extraction.jsonl.gz"),
]
GOLF = ROOT / "experiments" / "golf-v0.1"


def graph_row(source: str, record: dict[str, Any], extra: dict[str, Any] | None = None) -> dict[str, Any]:
    steps = counter.derive_steps(record["nodes"])
    parents = counter.dependency_graph(steps)
    analysis = counter.analyse(record)
    row = {"source": source, "module": record["module"], "declaration": record["declaration"],
           "steps": [{"kind": s["kind"], "line": s["line"]} for s in steps],
           "edges": [[p, i] for i, ps in enumerate(parents) for p in sorted(ps)],
           "forest": analysis["forest"], "roots": analysis["roots"],
           "linearizations": analysis["linearizations"], "structure": analysis["structure"]}
    return row | (extra or {})


def rows() -> list[dict[str, Any]]:
    out = []
    for source, path in SOURCES:
        out += [graph_row(source, record) for record in read_gz_lines(path)]
    pairs = {p["id"]: p for p in read_gz_lines(GOLF / "pairs.jsonl.gz")}
    for row in read_gz_lines(GOLF / "extraction.jsonl.gz"):
        if row["ok"] and row["record"] is not None:
            pair = pairs[row["pair"]]
            out.append(graph_row(f"golf-v0.1:{row['side']}", row["record"],
                                 {"pair": row["pair"], "commit": pair["commit"]}))
    return out


def serialize(data: list[dict[str, Any]]) -> bytes:
    return "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in data).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = serialize(rows())
    graphs = data.count(b"\n")
    if args.check:
        committed = gzip.decompress(OUTPUT.read_bytes())
        if hashlib.sha256(committed).hexdigest() != hashlib.sha256(data).hexdigest():
            raise SystemExit("the committed dataset does not follow from the committed extractions")
        print(f"dataset-check-ok: {graphs} graphs")
        return 0
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_bytes(gzip.compress(data, compresslevel=9, mtime=0))
    print(f"wrote {graphs} graphs to {OUTPUT.relative_to(ROOT)} "
          f"({OUTPUT.stat().st_size / 1e6:.1f} MB compressed)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
