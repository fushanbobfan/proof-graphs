#!/usr/bin/env python3
"""A proof whose goals share a metavariable passes the replay sample rule, and its other ordering fails.

  python scripts/check_coupled_orderings.py

orderings-replay-v0.1 drew small proofs whose goal-origin graphs are forests with one goal per step. That rule does
not test whether goals share a metavariable, and `fixtures/Coupled.lean` shows that it admits a proof whose goals do:
`refine ⟨?_, ?_⟩` leaves the witness `n` and the goal `?n + 1 = 5`, `exact 4` closes the first, `decide` the second.
This extracts the fixture, applies the experiment's own `eligible` rule to it, and replays both orderings with the
experiment's own `replay_order`: the original replays, and the other, which runs `decide` while the witness is still
a metavariable, fails on a tactic error. Lean core only, a few seconds after the build.
"""

from __future__ import annotations

import gzip
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from types import SimpleNamespace
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import count_linearizations as counter  # noqa: E402
import run_orderings_replay as replay  # noqa: E402
from lean_repl import LeanRepl  # noqa: E402
from run_linearizations import find_lake  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "fixtures" / "Coupled.lean"
STATEMENT = "∃ n : Nat, n + 1 = 5"


def errors(response: dict[str, Any]) -> list[str]:
    """The error messages of a response; the REPL reports a failed tactic as a top-level `message`."""
    found = [m.get("data", "") for m in response.get("messages", []) if m.get("severity") == "error"]
    return found + ([response["message"]] if "message" in response else [])


def main() -> int:
    lake = find_lake()
    extracted = subprocess.run([lake, "exe", "proof_graph_extract", "Coupled", str(FIXTURE)], cwd=ROOT, check=True,
                               capture_output=True, text=True, encoding="utf-8").stdout
    records = [json.loads(l) for l in extracted.splitlines() if l.strip()]
    record = next(r for r in records if r["declaration"] == "coupled_witness")
    steps = counter.derive_steps(record["nodes"])
    parents = counter.dependency_graph(steps)
    with tempfile.TemporaryDirectory() as scratch:  # the experiment's rule, run on the fixture as a one-proof corpus
        extraction = Path(scratch) / "extraction.jsonl.gz"
        extraction.write_bytes(gzip.compress(extracted.encode("utf-8")))
        replay.CORPORA["fixture"] = {"extraction": extraction, "source": FIXTURE.parent}
        admitted = [e for e in replay.eligible("fixture") if e["declaration"] == "coupled_witness"]
    texts = replay.step_texts(record, steps, FIXTURE.read_text(encoding="utf-8").split("\n"))
    produced = {g for s in steps for g in s["produced"]}
    root_goal = next(s["consumed"][0] for s in steps if s["consumed"][0] not in produced)
    orders = replay.linear_extensions(parents)

    repl = LeanRepl(lake, imports=None)
    try:
        def verify(_task: Any, script: list[str]) -> bool:
            body = "\n".join("  " + line for line in script)
            return not errors(repl._exchange({"cmd": f"example : {STATEMENT} := by\n{body}"}, 120))

        made = repl._exchange({"cmd": f"example : {STATEMENT} := by sorry"}, 120)
        task = SimpleNamespace(proof_state=made["sorries"][0]["proofState"])
        session = SimpleNamespace(verify=verify)
        outcomes = {tuple(o): replay.replay_order(repl, session, task, steps, texts, root_goal, o) for o in orders}
        # The failing step on its own, for its message.
        state = repl.tactic(task.proof_state, texts[0])
        assert state is not None
        moved = repl.tactic(state[1], "rotate_left 1")
        assert moved is not None
        message = " ".join(errors(repl._exchange({"tactic": texts[2], "proofState": moved[1]}, 60)))
    finally:
        repl.close()
    original, other = (0, 1, 2), (0, 2, 1)
    checks = {
        "the graph is a forest of three steps, each consuming one goal, with two orderings":
            len(steps) == 3 and all(len(p) <= 1 for p in parents) and all(len(s["consumed"]) == 1 for s in steps)
            and counter.forest_linearizations(parents) == 2 and sorted(orders) == [list(original), list(other)],
        "orderings-replay-v0.1's sample rule admits it": len(admitted) == 1,
        "the original order replays": outcomes[original].get("ok") is True,
        "the other order fails on a tactic error at decide":
            outcomes[other] == {"ok": False, "failure": "tactic error", "at": 1},
    }
    print(f"     steps: {texts}; decide with the witness unassigned: {message[:160]!r}")
    for name, ok in checks.items():
        print(f"{'ok  ' if ok else 'FAIL'} {name}")
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
