#!/usr/bin/env python3
"""goal_identity_typed's exporter on fixtures/identity_v2.lean, in a full-Mathlib REPL.

  python scripts/check_identity_v2_repl.py --built-checkout PATH

The REPL runs in a checkout whose Mathlib is built (`--built-checkout`, whose `scripts/lean_repl.py` starts it);
the module under test and the fixture come from this checkout. Each example's tactics before its `skip -- ID`
checkpoint are replayed in tactic mode, the goals at the checkpoint are exported, and the key relations the
fixture states are checked. Prints one line per checkpoint and per relation; exits non-zero on any failure.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIXTURE = HERE.parent / "fixtures" / "identity_v2.lean"
CHECKPOINT = re.compile(r"^\s*skip -- (\w+)")


def examples(text: str) -> list[tuple[str, str, list[str]]]:
    """(checkpoint id, header, tactics before the checkpoint) for every example with a checkpoint."""
    out = []
    for block in re.split(r"\n(?=example )", text):
        if not block.startswith("example "):
            continue
        header, _, body = block.partition(":= by\n")
        tactics: list[str] = []
        for line in body.splitlines():
            found = CHECKPOINT.match(line)
            if found:
                out.append((found.group(1), header.strip(), tactics))
                break
            if line.startswith("  ") and not line.startswith("   "):
                tactics.append(line[2:])
            elif line.startswith("   ") and tactics:
                tactics[-1] += "\n" + line[2:]
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--built-checkout", required=True, type=Path)
    args = parser.parse_args()
    sys.path.insert(0, str(HERE))
    sys.path.insert(0, str(args.built_checkout / "scripts"))  # lean_repl and find_lake from the built checkout
    import goal_identity_typed as gi  # noqa: E402
    from lean_repl import LeanRepl  # noqa: E402
    from run_linearizations import find_lake  # noqa: E402

    repl = LeanRepl(find_lake())
    exports: dict[str, list] = {}
    failures = 0
    try:
        for name, header, tactics in examples(FIXTURE.read_text(encoding="utf-8")):
            response = repl.command(f"{header} := by\n  sorry")
            sorries = response.get("sorries") or []
            if not sorries:
                print(json.dumps({"checkpoint": name, "ok": False, "error": response.get("messages")},
                                 ensure_ascii=False))
                failures += 1
                continue
            state = sorries[0]["proofState"]
            for tactic in tactics:
                stepped = repl.tactic(state, tactic)
                if stepped is None:
                    state = None
                    break
                state = stepped[1]
            goals = gi.export(repl, state) if state is not None else None
            ok = goals is not None
            failures += not ok
            if ok:
                exports[name] = goals
            print(json.dumps({"checkpoint": name, "ok": ok, "goals": None if goals is None else len(goals)}))
    finally:
        repl.close()

    def relation(label: str, holds: bool) -> None:
        nonlocal failures
        failures += not holds
        print(json.dumps({"relation": label, "ok": holds}, ensure_ascii=False))

    def single(name: str) -> str | None:
        return gi.goal_key(exports[name][0]) if name in exports else None

    def unordered(name: str) -> str | None:
        return gi.unordered_state_key(exports[name]) if name in exports else None

    def ordered(name: str) -> str | None:
        return gi.ordered_state_key(exports[name]) if name in exports else None

    def differ(a: str | None, b: str | None) -> bool:
        return a is not None and b is not None and a != b

    def equal(a: str | None, b: str | None) -> bool:
        return a is not None and a == b

    relation("S1 and S2 differ: literal markers stay literal", differ(single("S1"), single("S2")))
    relation("S3 and S4 differ", differ(single("S3"), single("S4")))
    relation("N1 and N2 agree: hypothesis names are erased", equal(single("N1"), single("N2")))
    relation("B1 and B2 agree: bound names are erased", equal(single("B1"), single("B2")))
    relation("B1 and B3 differ: binder info is kept", differ(single("B1"), single("B3")))
    relation("L1 and L2 agree", equal(single("L1"), single("L2")))
    relation("D1 and D2 agree: local definitions up to names", equal(single("D1"), single("D2")))
    relation("D1 and D3 differ: local definition values are kept", differ(single("D1"), single("D3")))
    relation("W1 and W2 agree unordered", equal(unordered("W1"), unordered("W2")))
    relation("W1 and W2 differ ordered", differ(ordered("W1"), ordered("W2")))
    relation("W1 and W3 differ unordered: independent witnesses", differ(unordered("W1"), unordered("W3")))
    relation("U1 and U2 agree unordered: joint level renaming", equal(unordered("U1"), unordered("U2")))
    relation("U1 and U3 differ unordered: level sharing is kept", differ(unordered("U1"), unordered("U3")))
    relation("U1 is one coupled group", "U1" in exports and gi.groups(exports["U1"]) == [[0, 1]])
    relation("U3 is two groups", "U3" in exports and gi.groups(exports["U3"]) == [[0], [1]])
    relation("W1 couples the witness and the two propositions",
             "W1" in exports and len(gi.groups(exports["W1"])) == 1)
    print(json.dumps({"failures": failures}))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
