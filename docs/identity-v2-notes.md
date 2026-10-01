# Goal identity v2 notes

## Built

- `scripts/goal_identity_typed.py`: JSON-tree exporter, ordered/unordered state keys, single-goal and
  coupled-group keys, and transitive term/universe coupling.
- `scripts/test_goal_identity_typed.py` and `scripts/test_audit_key_denominators.py`: pure Python
  regression tests on synthetic trees and logs, following the existing unittest style.
- `fixtures/identity_v2.lean`: adversarial checkpoints with expected equalities and differences.
- `scripts/audit_key_denominators.py` and `experiments/keys-v0.1-matched-support/{summary.json,README.md}`:
  matched-support duplicate shares and explicit false-identification denominators for all five arms.

## Interpretations

- The export uses `id`, `hyps`, and `target`, retaining the surrounding interface. Locals have type,
  optional value, binder info, and an implementation-detail flag; source names are omitted. Every local
  gets a context position, including implementation details. External free-variable ids stay opaque.
- Lean names are encoded as opaque strings containing canonical JSON of their structural name segments,
  preserving the distinction between escaped string segments, numerical segments, and dotted names.
- All own goal metavariables are numbered before traversing contexts and targets. Traversal then visits
  each local's type before its value, and visits expression/level children in constructor order. Term
  and level numbering are separate. Normalized own goal ids are retained, including repeated goal ids;
  repeated occurrences of the same open goal belong to one coupled group.
- Keys use canonical JSON and 16 hexadecimal SHA-256 digits, matching the earlier digest length.
  Unordered identity enumerates permutations before hashing, with the specified default bound of seven.
  `None` is an unavailable key, never an equality class. Single-goal keys cannot test state sharing.
- Let trees retain type, value, and body, as specified, and omit the binder name and `nondep` flag.
  Metadata nodes disappear. Failure in any goal invalidates the complete export; Python also rejects
  malformed trees. A named pre-defined tactic is an optional argument to `export`.
- Coupling covers occurrences in local types, local definition values, targets, and universe trees.
  Its contract excludes hidden delayed-assignment dependencies and tactic side state.
- The audit's expression keys are the committed v1 digests. Duplicate histories start empty per unit,
  count first goals only, and insert only exported expansions into both histories. False-drop and
  false-merge histories retain the original search decisions, including missing exports; their shares
  divide by evaluable endpoint comparisons. Unlogged units have unknown expansions/decisions, not zero.
- The audit reads the three source artifacts from HEAD. It reports source digest discrepancies rather
  than replacing blobs, and checks gzip decoding, unit coverage, expansion counts, reconstructed drop
  decisions, and the committed per-unit false-identification counts. Existing outputs are never
  overwritten: `--check` recomputes and compares them byte for byte.

## Limits and findings

The Lean exporter and fixture have not been compiled or run. The existing modules remain unchanged;
future callers must explicitly select the typed module. No goal-selection work is included.

The logs lack expression trees needed for v2 re-keying. For renamed AND-OR, they also lack accepted
merge decisions, alias-to-node mappings, accepted renaming targets, and the goal text required to
reconstruct `renaming_step`/`agrees`. Its false-merge counts and share remain unavailable; coarse-key
matches are not used as a proxy. These limits are explicit in the audit artifacts.

The committed logs blob has SHA-256
`70de16d1f5003a562a79a8a65d45226d5b199f851d429c9a73318d2c26d9590c`, whereas the source summary records
`b9b60174d1e500fb3fb2978eabf80857ea93ff348cd314d94cce45ac76b77603`. Its cause is unconfirmed. The blob
decodes successfully, covers all 932 audited units, and reproduces their decision counts. Results.jsonl
matches its recorded digest. The discrepancy is retained in `sourceHashChecks` and the audit README.

Pooled whole-state false drops are 794 of 13,993 evaluable comparisons (5.6743%), with 256 missing out
of 14,249 total. Printed AND-OR false merges are 244 of 2,739 evaluable comparisons (8.9084%), with
70 missing out of 2,809 total. Matched-support duplicate counts and shares are in the audit README.

Validation commands: `python -B -m unittest discover -s scripts -p "test_*.py"` and
`python -B scripts/audit_key_denominators.py --check`. Python tests cover typed normalization, bounded
permutation canonicalization, coupling, export failure handling, and the audit's denominator rules.
