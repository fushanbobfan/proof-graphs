# What defeq-v0.1's merges bridge (not registered)

defeq-v0.1 found that identity up to definitional equality adds 150 goal duplicates to the step prover's whole-state
search, all at reducible transparency, but its logs keep only hashes of the printed goals. This exploratory replay,
made after defeq-v0.1's results were read, looks at what the merged goals differ in. It replays the 43 step-prover
units with such a duplicate, merges their goals again at reducible transparency, as the registered merge does, and
classifies each merged pair in Lean by the first of these erasures that makes the two closed types equal:

1. none: the closed types are equal after the merge's beta-reduction and level normalization. The two expression
   keys are then compared with their let-bound hypotheses dropped and the rest renumbered, since the closed type
   leaves out let-bound hypotheses the goal does not use, which are equal up to zeta-reduction whatever their types
   and values; printed closed types that differ but normalize alike are beta-reduction or universe levels;
2. binder names and kinds;
3. proof subterms;
4. instance arguments;
5. instance arguments and proofs;
6. implicit arguments and proofs;
7. none of these: the pair needs unfolding.

An erased subterm becomes `sorryAx` of its type, so two erased subterms are equal exactly when their types are. Each
added duplicate is attributed to the merge that joins its first goal to the earlier first goal of its class.

## Artifacts

- `rows.jsonl`: per unit, every merged pair with its class, its round-trip statuses, and the first difference of
  both its printed closed types and its expression keys; and every added duplicate with its class;
- `summary.json`: the counts by class, per unit, and examples.

## Reproduction

```text
python scripts/explore_defeq_merges.py --check
```

recomputes the summary from the rows; CI runs it. `--run` replays the units (a Mathlib REPL each; about twenty
minutes on three workers).

## Outcome

42 of the 43 units were classified; in `AlgebraicGeometry.injective_germ_basicOpen`, whose goals print to about
120,000 characters, the erasures ran out of heartbeats, so its 5 added duplicates are not classified.

| What the merged goals differ in | Added duplicates | Merged pairs |
| --- | ---: | ---: |
| let-bound hypotheses the goal does not use | 102 | 303 |
| nothing in the closed type, but more than unused let hypotheses by the text check | 9 | 26 |
| instance arguments | 20 | 63 |
| beta-reduction or universe levels | 7 | 23 |
| implicit arguments and proofs | 4 | 17 |
| proof subterms only | 1 | 4 |
| needs unfolding | 2 | 4 |
| total | 145 | 440 |

- Most of the added duplicates (102 of 145) join goals whose targets and other hypotheses are equal and whose
  contexts differ only in let-bound hypotheses the goal does not mention: for instance `x : ℝ := √5` against
  `x : ℝ := (1 + √5) / 2` in `Real.goldenRatio_irrational`, or two different such definitions. The expression key
  writes a let-bound hypothesis with its value; the closed type drops it when nothing uses it. The five of the nine
  next ones inspected also differ in let-bound hypotheses, such as an instance `DecidableEq α := Classical.decEq α`
  or a witness `ι := Classical.arbitrary ι`, at different places in the context.
- 20 are instance paths, the same operation reached through different instances, as `instHMul ℕ
  (Semigroup.toMul ℕ Nat.instSemigroup)` against `instHMul ℕ instMulNat`; 7 are universe levels written differently
  (`(max u₁ u₂) + 1` against `max (u₁ + 1) (u₂ + 1)`) or an unreduced lambda; the rest differ in implicit type
  arguments that unfold alike (`Ideal R` against `Submodule R R`), in a proof (`of_eq_true (eq_true h)` against
  `h`), or in an auxiliary proof against its unfolding.

So the step prover's added duplicates are mostly not variant spellings of one term but goals that differ in let
hypotheses the goal does not mention. The step prover proposes the steps that introduce them: 3,082 of the 92,462
candidates recorded for these searches start with `let`, `letI` or `set`. The menu's 26 fixed candidates include none
of these, which fits its gain of 0.1 points (an inference; the menu's merges were not classified).

## Interpretation boundary

The classification is the first erasure that equates a pair, in a fixed order, so a pair that differs in several ways
is counted once; "nothing in the closed type" covers every difference the closed type drops, of which unused let
hypotheses are the only kind found. Whether two goals that differ in unused let hypotheses should count as one goal
is a matter of definition: their closed types are equal up to zeta-reduction, and a proof of one is a proof of the
other once those hypotheses are cleared.
