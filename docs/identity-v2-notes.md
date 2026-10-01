# Goal identity v2

`scripts/goal_identity_typed.py` identifies goals and proof states on typed expression trees exported from
Lean, for new experiments. It fixes four defects of the text keys in `scripts/goal_identity.py`: string
literals rewritten as metavariables, order duplicates judged on goals normalized one by one (losing shared
witnesses), out-of-context free variables collapsed to one placeholder with implementation-detail locals
dropped, and coupling blind to universe metavariables. The registered experiments keep the old module,
which is unchanged.

## Contents

- `scripts/goal_identity_typed.py`: the exporter (`KEY_TACTIC`, run directly or defined once as a tactic),
  ordered and unordered state keys, single-goal and coupled-group keys, and transitive term and universe
  coupling.
- `scripts/test_goal_identity_typed.py`, `scripts/test_audit_key_denominators.py`: tests on synthetic trees
  and logs, without Lean.
- `fixtures/identity_v2.lean`, `scripts/check_identity_v2_repl.py`: adversarial checkpoints (string
  literals, escaped and Unicode names, binders, local definitions, shared existential witnesses, universe
  metavariables), replayed in a full-Mathlib REPL with their stated equalities and differences checked.
- `scripts/audit_key_denominators.py`, `experiments/keys-v0.1-matched-support/`: keys-v0.1's duplicate
  shares on matched support and its false identifications with explicit denominators.

## Design

- The export gives each goal its `id`, `hyps`, and `target`. A local has a type, an optional value, binder
  info, and an implementation-detail flag; names are omitted. Every local gets a context position,
  implementation details included, and a free variable outside the context keeps its own id.
  Metavariables are instantiated and metadata dropped before export.
- The exporter serializes with an explicit stack. `run_tac` evaluates its term without lifting `let rec`
  definitions, so a recursive serializer fails there with "failed to evaluate expression, it contains
  metavariables".
- A Lean name is an opaque string holding a JSON array of its components, strings and numbers kept apart.
- Renumbering numbers a goal list's own goal ids first, then visits each local's type before its value,
  then the target, children in constructor order. Term and level metavariables have separate numberings.
  Repeated goal ids are kept and fall in one coupled group.
- A key is 16 hexadecimal digits of the SHA-256 of canonical JSON. The unordered key sorts the goals by
  their own keys (`goal_key`, which no joint renaming or reordering changes) and minimizes the joint
  serialization over the orders of tied goals only. Two states therefore get equal keys exactly when one
  is a reordering and joint renaming of the other, and a state without ties costs one serialization. The
  key is `None` when ties admit more than 5,040 orders, so every state of up to seven goals has one;
  `None` is never a merge key. A single-goal key cannot see sharing between goals.
- Let trees keep type, value, and body, without the binder name or `nondep` flag. A failure in any goal
  fails the whole export, and Python rejects malformed trees.
- Coupling covers metavariable occurrences in local types, local definition values, targets, and universe
  trees. It does not see dependencies through delayed assignments whose metavariables do not occur, or
  through tactic side state.

## Audit of keys-v0.1

The audit uses the committed v1 expression-key digests and reads its sources from HEAD; their digests
match those recorded in keys-v0.1's summary (a `.gz` file is hashed by its decompressed content, as the
runners do). Duplicate histories start empty in each unit, count first goals only, and take only exported
expansions, in both histories alike. False-drop and false-merge histories keep the original search's
decisions, missing exports included; their shares divide by the comparisons whose endpoints both exported.
Unlogged units have unknown expansions and decisions, not zero. `--check` recomputes the outputs and
compares them byte for byte.

Pooled whole-state false drops are 794 of 13,993 evaluable comparisons (5.67%), 256 missing of 14,249.
Printed AND-OR false merges are 244 of 2,739 (8.91%), 70 missing of 2,809. Duplicate shares per arm are in
the audit README.

The logs hold v1 digests only, so v2 keys cannot be recomputed from them; re-keying needs a replay in Lean.
For renamed AND-OR they also lack the accepted merge decisions, alias-to-node mappings, accepted renaming
targets, and goal text needed to rebuild `renaming_step` and `agrees`, so its false merges remain
unavailable; coarse-key matches are not used as a proxy.

## Validation

    python -B -m unittest discover -s scripts -p "test_*.py"
    python -B scripts/audit_key_denominators.py --check
    python -B scripts/check_identity_v2_repl.py --built-checkout PATH

The last needs a checkout whose Mathlib is built; it exports 20 checkpoints and checks 16 relations.
