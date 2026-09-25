# Blind reconstruction of goal-dependency graphs (extraction audit v0.1)

Sample, protocol, and hypothesis are frozen in `preregistration.json` (SHA-256
`8d27d090c35ea5dd1a26371857dce62accda5f4b4fa666f94b79212ca99fb410`).

Proofs: 30; graphs agree: 29; ordering counts agree: 29.

| Corpus | Stratum | Declaration | Steps (derived / rebuilt) | Agree |
| --- | --- | --- | ---: | --- |
| proofnet-ir | 2-5 | `ProofNetIR.SequentialFigure7.unifyPayload?_exists_of_enabled` | 2 / 2 | yes |
| proofnet-ir | 2-5 | `ProofNetIR.Certificate.referenceOwnedGraph_edge_mem` | 3 / 3 | yes |
| proofnet-ir | 2-5 | `ProofNetIR.Certificate.requeueWaiting_successfulFirings` | 2 / 2 | yes |
| proofnet-ir | 2-5 | `ProofNetIR.Graph.isTree_reindex` | 4 / 4 | yes |
| proofnet-ir | 2-5 | `ProofNetIR.Certificate.restrictTo?_conclusions` | 5 / 5 | yes |
| proofnet-ir | 6-10 | `ProofNetIR.Certificate.restrictTo?_formula?_idxOf` | 7 / 7 | yes |
| proofnet-ir | 6-10 | `ProofNetIR.Certificate.distinct_mem_ordered_decomposition` | 9 / 9 | yes |
| proofnet-ir | 6-10 | `ProofNetIR.Certificate.UnificationComponent.FormulaConsistent.tensor` | 7 / 7 | yes |
| proofnet-ir | 6-10 | `ProofNetIR.Certificate.producerCount_eq_zero_of_no_connective` | 7 / 7 | yes |
| proofnet-ir | 6-10 | `ProofNetIR.SequentialFigure7.DispatchTagEvidence.oldContinuationCredit` | 7 / 7 | yes |
| proofnet-ir | 11-20 | `ProofNetIR.Certificate.CuspFreeContinuation.firstIntersection_withCycle_cycle` | 11 / 11 | yes |
| proofnet-ir | 11-20 | `ProofNetIR.SequentialFigure7.UnifyOneStep.tensorPremisesMarkedAfter` | 20 / 20 | yes |
| proofnet-ir | 11-20 | `ProofNetIR.SequentialFigure7.ForwardInput.queue_data_exists` | 11 / 11 | yes |
| proofnet-ir | 11-20 | `ProofNetIR.Certificate.length_le_of_nodup_subset` | 19 / 19 | yes |
| proofnet-ir | 11-20 | `ProofNetIR.length_filter_filterMap_eq` | 20 / 22 | no |
| mathlib-slice | 2-5 | `RCLike.I_im'` | 3 / 3 | yes |
| mathlib-slice | 2-5 | `Topology.CWComplex.union` | 3 / 3 | yes |
| mathlib-slice | 2-5 | `IsAzumaya.mulLeftRight_comp_congr` | 3 / 3 | yes |
| mathlib-slice | 2-5 | `RCLike.abs_im_le_norm` | 4 / 4 | yes |
| mathlib-slice | 2-5 | `Ideal.Quotient.isUnit_mk_pow_iff_notMem` | 4 / 4 | yes |
| mathlib-slice | 6-10 | `ringExpChar.eq` | 8 / 8 | yes |
| mathlib-slice | 6-10 | `SimpleGraph.ediam_le_two_mul_radius` | 10 / 10 | yes |
| mathlib-slice | 6-10 | `RCLike.norm_le_im_iff_eq_I_mul_norm` | 9 / 9 | yes |
| mathlib-slice | 6-10 | `Nat.abundant_iff_two_lt_abundancyIndex` | 8 / 8 | yes |
| mathlib-slice | 6-10 | `FirstOrder.Language.Formula.realize_equivSentence_symm_con` | 7 / 7 | yes |
| mathlib-slice | 11-20 | `ProbabilityTheory.Kernel.partialTraj_succ_map_frestrictLe₂` | 18 / 18 | yes |
| mathlib-slice | 11-20 | `Subalgebra.rank_sup_le_of_free` | 15 / 15 | yes |
| mathlib-slice | 11-20 | `ContinuousLinearMap.nnnorm_def` | 11 / 11 | yes |
| mathlib-slice | 11-20 | `Sigma.subtype_ext_iff` | 13 / 13 | yes |
| mathlib-slice | 11-20 | `ConvexOn.map_condExp_le` | 15 / 15 | yes |

## Disagreements

- `ProofNetIR.length_filter_filterMap_eq`: extractor error. The graphs agree except that the derived one lacks the two `simpa [equation] using ...` steps at lines 245 and 249 and their edges from the `have` steps at 244 and 248. Each `simpa` node closes the goal its `have` created (goal before, none after), but its own internal child node lists that goal before it and leaves it as it was, and the rule counts a goal as consumed only if no later node mentions it, the node's own descendants included. The goal is therefore consumed by no step and the closing step is lost; the reconstruction, which records both steps, is right. The reconstructor's note attributes the difference to `cases h : e with`, but both graphs have two steps for each of those. With later nodes inside the node's own subtree ignored, the derived graph equals the reconstruction; that correction is scripts/count_linearizations_v2.py, and recount-v0.1 applies it to every committed extraction.

H26 (no extractor error): supported: False.
