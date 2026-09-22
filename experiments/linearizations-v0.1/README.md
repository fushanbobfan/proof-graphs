# Linearizations v0.1

Step 1 of the program ([design](../../docs/design.md)): how many orderings of
its steps every tactic proof of ProofNet-IR v0.10.0 admits, exactly, from the
goal-dependency graph extracted out of Lean's info trees.

## Artifacts

- `preregistration.json`: the dependency revision, the 190-module list, the
  extractor and counter hashes, the strata, hypotheses H10 and H11, and the
  statement that no corpus count existed; committed on `main` before the run;
- `amendment-1.json` to `amendment-5.json`: the changes made after the
  first extraction failed, each with the hashes it replaces: nodes split per
  declaration and the extraction compressed; steps derived from goal origins
  after a validation sample showed bogus roots; quartiles of counts in
  integer arithmetic; after the corpus had been counted once, failed
  alternatives of `first`/`try`/`repeat` dropped and delegated origins
  merged, with the first count's table recorded in the amendment; and a
  platform-independent module order for the check;
- `extraction.jsonl.gz`: every tactic node of every declaration (goals
  before and after, parent, leaf flag, syntax kind, line), 3,994 records;
- `results.jsonl`: one row per declaration with the step count, the forest
  flag, the number of roots, the exact count as a decimal string, its base-10
  logarithm, and the structure index;
- `summary.json` and `report.md`: per-stratum quartiles, the hypothesis
  decisions, and the artifact hashes.

## Reproduction

```text
python scripts/run_linearizations.py --check-committed
```

recounts every committed graph, re-extracts `ProofNetIR.Formula`,
`ProofNetIR.Certificate`, and `ProofNetIR.Figure7.Cost` and compares the node
shapes, and verifies the artifact hashes; CI runs it. `--run` re-extracts all
190 modules (about 16 minutes, one process per module); `--recount` rewrites
the results from the committed extraction in seconds.

## Outcome

3,994 declarations in 183 modules have tactic steps; 3,992 are counted
exactly. Eight graphs are not forests (an `exact` or `rw` that also assigns
a metavariable of an earlier `apply`), two of them too large for the subset
enumeration (363 and 29 steps) and excluded as registered. 71 declarations
have more than one root, all with several root blocks: `by` blocks in
term-mode match alternatives, in structure fields, or in the arguments and
statements of a declaration (56), and functions with `decreasing_by`
obligations (15); a `by` inside a statement counts as a step of that
declaration, one independent root.

| Steps | Proofs | Linearizations median (max) | Structure median | Single order |
| --- | ---: | --- | ---: | ---: |
| 2–5 | 1,220 | 1 (60) | 0.000 | 59.6% |
| 6–10 | 828 | 15 (51,840) | 0.255 | 15.3% |
| 11–20 | 845 | 6,720 (8.4·10^14) | 0.337 | 1.8% |
| 21–50 | 588 | 8.8·10^13 (1.7·10^42) | 0.413 | 0.0% |
| 51+ | 263 | 1.9·10^51 (1.3·10^628) | 0.502 | 0.0% |

- H10 supported: the median number of orderings is at least 10 in every
  stratum from 6 steps on, and grows super-exponentially with length; the
  largest proof (461 steps) admits 1.3·10^628 orderings.
- H11 not supported as registered: the median structure index stays below
  0.5 up to 50 steps but is 0.502 at 51 steps and more, on the threshold.
  Longer proofs are more parallel, not less: they are mostly `have` chains
  whose subproofs are independent of each other. The 21 generated
  declarations (derived instances, `ext` and `ext_iff`) do not move the
  medians (hand-written 51+: 0.502).

Only 23.2% of the proofs with at least two steps admit a single order; from
11 steps on, almost none does. The first count, before amendment 4, gave the
same verdicts with 0.508 in the last stratum.

## Interpretation boundary

The count is the order redundancy a search faces when it may work on any open
goal, as a sequent-calculus search may decompose any formula. Lean's tactic
framework acts on the first goal: that convention is one linearization of
the graph, depth-first in production order, and a search that keeps to it
and has no goal-selecting tactic (`case`, `swap`, `rotate_left`, `on_goal`)
generates no two states that differ only in goal order. What this experiment
measures is therefore the redundancy the framework's convention removes, not
a cost a first-goal search pays; what remains for a search lives in goal
selection, in combinators such as `<;>` and `·`, and in nested `by` blocks.
Nothing here says anything about proofs outside this corpus, whose style is
one author's, or about different tactic paths to the same goal.
