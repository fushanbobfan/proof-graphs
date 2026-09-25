# Extraction audit v0.1

Is the derived goal-dependency graph the graph the definition describes? For
30 proofs drawn at random (seed 20260925; 15 from ProofNet-IR v0.10.0 and 15
from the Mathlib slice; 5 per stratum of 2 to 5, 6 to 10, and 11 to 20
steps), two reconstructors that never saw the derived graphs rebuilt each
graph from the source and Lean's goal display, following the definition in
the docstring of `scripts/count_linearizations.py`; the comparison then matched
steps by source line and compared edges.

## Artifacts

- `preregistration.json`, `sample.json`: the sample rule, the protocol, the
  disagreement categories, and hypothesis H26; `amendment-1.json`, made before
  any reconstruction existed, records that the reconstructors are two separate
  language-model agent instances with Lean language-server access (one per
  corpus), not people, and quotes everything they were told;
- `reconstructions.json`: their graphs and notes, committed before the first
  comparison;
- `results.jsonl`, `summary.json`, `report.md`: the comparison;
- `adjudication.json`: the classification of each disagreement, with its
  evidence.

## Reproduction

```text
python scripts/run_extraction_audit.py --check-committed
```

recomputes the comparison from the committed reconstructions and extractions;
CI runs it.

## Outcome

29 of the 30 graphs agree exactly, steps and edges, including proofs of 18
and 20 steps. **H26 not supported**: the one disagreement is an extractor
error. In `ProofNetIR.length_filter_filterMap_eq` the derived graph lacks two
`simpa ... using ...` steps. Each closes the goal its `have` created, but its
own internal node mentions that goal before leaving it unchanged, and the rule
let any later node, the step's own descendants included, keep a goal open. The
closing step was lost.

The defect is not rare. `scripts/count_linearizations_v2.py` ignores later
nodes inside the step's own subtree; under it the derived graph equals the
reconstruction here, all 30 reconstructions agree, the structural invariants
hold for every graph, and the six fixtures keep their counts. It changes the
steps of 838 of the 3,994 ProofNet-IR graphs, 114 of the 2,807 slice graphs,
and 40 of the 484 golf graphs, almost all by adding `simpa` steps.
[recount-v0.1](../recount-v0.1/README.md) applies it to every committed
extraction.

## Interpretation boundary

The reconstructors are model agents, so this is an independent automated
check, not a human one; a person's reconstruction of a subsample remains the
stronger check. `sample.json` gave each proof's step-count stratum, which both
reconstructors report having used as a cross-check; one reconstruction fell
outside its stratum and was kept as reconstructed. The sample is 30 proofs of
at most 20 steps, drawn by step count, not by tactic kind.
