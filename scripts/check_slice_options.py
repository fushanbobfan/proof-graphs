#!/usr/bin/env python3
"""Do Mathlib's elaboration options change the slice's graphs?

  python scripts/check_slice_options.py [--workers 6]

`linearizations-mathlib-v0.1` extracted its 157 modules under Lean's
default options. Mathlib builds with `autoImplicit false` and
`maxSynthPendingDepth 3`. This check re-extracts every slice module from its
v4.32.0 text with those two options inserted after the header (as
`scripts/run_golf.py` does), and compares each declaration with the
committed extraction: the node shapes (index, parent, leaf flag, syntax kind,
goal counts before and after) and the counted steps and orderings, per
distinct declaration name (the few names a file repeats are compared by
their last record on both sides). It writes
`experiments/linearizations-mathlib-v0.1/options-check.json`; it changes no
committed result.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import re
import sys
import tempfile
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_golf as golf  # noqa: E402
import run_mathlib_slice as slice_  # noqa: E402
from run_linearizations import count, read_gz_lines, write_lf  # noqa: E402

OUTPUT = slice_.EXPERIMENT / "options-check.json"


def shape(record: dict[str, Any]) -> list[tuple[Any, ...]]:
    return [(n["index"], n["parent"], n["leaf"], n["kind"], len(n["before"]), len(n["after"]))
            for n in record["nodes"]]


def extract_with_options(module: str, scratch: Path) -> tuple[list[dict[str, Any]], str]:
    """The module's records under Mathlib's options. A name the extractor
    suffixed with a line (`:L<n>`, for names repeated in one file) gets the
    inserted lines subtracted, so that it matches the committed name."""
    text, shift = golf.with_mathlib_options(golf.module_text(module))
    path = scratch / f"{module.replace('.', '_')}.lean"
    path.write_bytes(text.encode("utf-8"))
    records, diagnostics = golf.extract_file(module, path)
    path.unlink()
    for record in records:
        record["declaration"] = re.sub(r":L(\d+)$", lambda m: f":L{int(m.group(1)) - shift}", record["declaration"])
    return records, diagnostics


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=6)
    args = parser.parse_args()
    committed: dict[tuple[str, str], dict[str, Any]] = {
        (r["module"], r["declaration"]): r for r in read_gz_lines(slice_.EXTRACTION)}
    committed_rows = {(r["module"], r["declaration"]): r for r in
                      (json.loads(l) for l in slice_.RESULTS.read_text(encoding="utf-8").splitlines() if l.strip())}
    modules = [name for name, _ in slice_.modules()]
    fresh: dict[tuple[str, str], dict[str, Any]] = {}
    module_errors: dict[str, str] = {}
    with tempfile.TemporaryDirectory(prefix="slice-options-") as scratch, \
            concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(extract_with_options, m, Path(scratch)): m for m in modules}
        for done, future in enumerate(concurrent.futures.as_completed(futures), 1):
            module = futures[future]
            records, diagnostics = future.result()
            if "errors=0" not in diagnostics:
                module_errors[module] = diagnostics
            for record in records:
                fresh[(record["module"], record["declaration"])] = record
            print(f"{done}/{len(modules)} {module}", flush=True)
    counted = {(r["module"], r["declaration"]): c for r, c in zip(fresh.values(), count(list(fresh.values())))}
    same_shape, differing, missing, added = 0, [], [], []
    for key, record in committed.items():
        if key[0] in module_errors:
            continue
        if key not in fresh:
            missing.append(key)
        elif shape(fresh[key]) == shape(record):
            same_shape += 1
        else:
            old, new = committed_rows[key], counted[key]
            differing.append({"module": key[0], "declaration": key[1],
                              "steps": [old["steps"], new["steps"]],
                              "linearizations": [old["linearizations"], new["linearizations"]]})
    added = [key for key in fresh if key not in committed and key[0] not in module_errors]
    count_changed = [d for d in differing if d["steps"][0] != d["steps"][1] or d["linearizations"][0] != d["linearizations"][1]]
    report = {"modules": len(modules), "modulesWithErrors": module_errors,
              "declarationsCompared": sum(1 for k in committed if k[0] not in module_errors),
              "sameShape": same_shape, "differentShape": len(differing),
              "differentCounts": len(count_changed), "differing": differing,
              "missing": [list(k) for k in missing], "added": [list(k) for k in added]}
    write_lf(OUTPUT, json.dumps(report, indent=1, ensure_ascii=False) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in ("differing", "missing", "added")} |
                     {"missing": len(missing), "added": len(added)}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
