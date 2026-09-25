# Search v0.1

Steps 2 and 3 of the program ([design](../../docs/design.md)): how much of a
real tactic search is spent on states that differ only in goal order, how
much on goals another branch already expanded, and whether searching over
goals instead of whole states proves more at equal budget.

## Artifacts

- `preregistration.json` and `tasks.json`: the 47 tasks (theorems of the
  [Mathlib slice](../linearizations-mathlib-v0.1/README.md) whose proof is one
  `by` block of 3 to 20 steps, every 29th of 1,347 candidates in (module,
  line) order), the two proposer arms, the two searches, the budget, the
  measures, and hypotheses H14 to H16b; committed on `main` before any run;
- `amendment-1.json`, `amendment-2.json`: the changes made after two runs
  were discarded, with the numbers seen before each: a REPL per module and
  declaration prefixes kept; then the entanglement rule, `sorry` refused, and
  verification moved inside the searches;
- `results.jsonl`: one row per task with, for each arm and search, every
  expansion, the proof, and the counters;
- `model-calls.jsonl.gz`: the 4,500 prompts and replies of the model arm;
- `summary.json`, `report.md`: the per-arm table and the hypothesis decisions.

## Reproduction

```text
lake exe cache get && lake build repl
python scripts/run_search.py --check-committed
```

recomputes the summary from the committed rows and re-runs the first task's
menu whole-state search for four expansions, comparing it with the committed
one; CI runs it (about a minute). `--run` repeats the experiment (three
hours; the model arm needs a local OpenAI-compatible server on port 8080) and
resumes from `results.jsonl` if interrupted.

## Outcome

40 of the 47 tasks could be stated in context; the other seven are term-mode
proofs with a nested `by`, a `def`, or an `ext_iff` companion, which the task
rule (one `by` block in the extracted graph) does not separate. Two modules
reported elaboration errors in their prefix and their tasks are among those
seven.

| Arm | Whole-state expansions | Order duplicates | Goal duplicates | Valid tactics per expansion | Proved: whole | Proved: AND-OR | Entangled candidates |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| menu | 448 | 15 (3.3%) | 48 (10.7%) | 3.3 | 5 | 4 | 63 |
| model | 556 | 13 (2.3%) | 48 (8.6%) | 4.0 | 5 | 5 | 67 |

- **H14 not supported**: 3.3% and 2.3% of the expansions are states whose
  goal multiset had already been expanded in another order, above the
  registered 1%. The mechanism is not goal selection: `symm` before
  `constructor` on an `↔` yields the same two subgoals in the other order, as
  does `constructor` after a commuting rewrite. Order redundancy survives the
  first-goal convention, but it is a few percent, not the factorial of
  step 1.
- **H15 not supported**, and only just: the goal-duplicate fraction is 10.7%
  in the menu arm and 8.6% in the model arm, against a registered threshold
  of 10% in *both*. 11 of the 40 tasks have at least one such expansion, most
  of them `↔` goals where both branches re-attack the same side.
- **H16a not supported**: with the same budget the AND-OR search proves 4 and
  5 tasks against 5 and 5. Six tasks are proved by some search, four of them
  by every search in one expansion (`aesop`, `simp`, `exact?`). The two
  differences are single tasks: the whole-state search proves
  `Set.iUnion_finset_eq_set` at expansion 12 while the AND-OR search spends
  its budget on other goals; the model AND-OR search proves
  `List.length_erase_add_one` in three expansions, which no whole-state
  search found.
- **H16b not supported**: in the model arm both searches prove 5 tasks.

The AND-OR search pays for what it saves: 68 and 73 `pick_goal` calls, and
63 and 67 candidates discarded as entangled — a tactic on the goal changed
another open goal, because they share a metavariable. That is 4% and 3% of
the candidates it could otherwise have used, and it is the price of treating
goals as independent. Mature goal searches do not pay it in this form:
HyperTree Proof Search keeps goals that share a metavariable together, and
Aesop copies the coupled goals into the assigning rule application; this
search treats every goal as independent on purpose, to measure how often the
assumption fails.

## Interpretation boundary

Both searches are breadth-first with 24 expansions and a weak proposer
(a 26-tactic menu; a 35B local model at 15 tokens a reply, sampled four
times). 13 to 18 tasks per arm exhausted the budget and 17 to 24 exhausted
their frontier, so these numbers describe where such a search spends its
expansions, not the best achievable prover; a stronger proposer would move
both the proof counts and the duplicate fractions. A proof counts only when
its script re-verifies from the statement in the theorem's own context, and
`sorry` is not progress. The REPL elaborated each module under Lean's default
options rather than those of Mathlib's build (`autoImplicit false`,
`maxSynthPendingDepth 3`); every search and arm shares this, so the
comparisons stand, but a tactic that needs the deeper instance synthesis
fails here.
