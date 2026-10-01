# Goal-selection diagnostic v0.1

Constructed tasks, each posed with a fixed prefix; cells give expansions and candidate applications, with the applications at the proof, or a dash without a proof.

| Task | Kind | firstText | first | any | anyMultiset |
| --- | --- | ---: | ---: | ---: | ---: |
| square_sixteen | coupled | 24 / 624, - | 24 / 624, - | 11 / 703 | 10 / 625 |
| affine_seven | coupled | 24 / 624, - | 24 / 624, - | 12 / 781 | 11 / 703 |
| mod_five | coupled | 24 / 624, - | 24 / 624, - | 11 / 703 | 10 / 625 |
| triple_twelve | coupled | 24 / 624, - | 24 / 624, - | 11 / 703 | 10 / 625 |
| truncated_sub | coupled | 24 / 624, - | 24 / 624, - | 11 / 703 | 10 / 625 |
| sub_from_ten | coupled | 24 / 624, - | 24 / 624, - | 11 / 703 | 10 / 625 |
| half_eight | coupled | 24 / 624, - | 24 / 624, - | 11 / 703 | 10 / 625 |
| cube_eight | coupled | 24 / 624, - | 24 / 624, - | 11 / 703 | 10 / 625 |
| pair_sum | coupled | 24 / 624, - | 24 / 624, - | 24 / 2860, - | 24 / 2756, - |
| pair_product | coupled | 24 / 624, - | 24 / 624, - | 24 / 2860, - | 24 / 2756, - |
| two_facts | independent | 2 / 27 | 2 / 27 | 2 / 53 | 2 / 53 |
| order_facts | independent | 2 / 27 | 2 / 27 | 2 / 53 | 2 / 53 |
| divisibility | independent | 2 / 27 | 2 / 27 | 2 / 53 | 2 / 53 |
| three_facts | independent | 5 / 105 | 5 / 105 | 11 / 703 | 11 / 703 |
| true_and_sum | independent | 2 / 27 | 2 / 27 | 2 / 53 | 2 / 53 |
| quotient_square | independent | 2 / 27 | 2 / 27 | 2 / 53 | 2 / 53 |
| forall_first | independent | 2 / 27 | 2 / 27 | 2 / 53 | 2 / 53 |
| comm_first | independent | 2 / 27 | 2 / 27 | 2 / 53 | 2 / 53 |

## Predictions

| Item | Statement | Result |
| --- | --- | --- |
| D1 | No coupled task is proved by first or by firstText. | holds |
| D2 | Every coupled task is proved by any and by anyMultiset. | fails |
| D3 | Every proof of a coupled task found by any or anyMultiset acts, at some step, on a goal other than the first that shares a metavariable with another open goal (coupling replay of the found proof). | holds |
| D4 | Every independent task that some arm proves is proved by first. | holds |

## Proofs found

- square_sixteen, any: `pick_goal 3; rfl; simp` (coupled choice: True)
- square_sixteen, anyMultiset: `pick_goal 3; rfl; simp` (coupled choice: True)
- affine_seven, any: `pick_goal 3; rfl; simp` (coupled choice: True)
- affine_seven, anyMultiset: `pick_goal 3; rfl; simp` (coupled choice: True)
- mod_five, any: `pick_goal 3; rfl; simp` (coupled choice: True)
- mod_five, anyMultiset: `pick_goal 3; rfl; simp` (coupled choice: True)
- triple_twelve, any: `pick_goal 3; rfl; simp` (coupled choice: True)
- triple_twelve, anyMultiset: `pick_goal 3; rfl; simp` (coupled choice: True)
- truncated_sub, any: `pick_goal 3; rfl; simp` (coupled choice: True)
- truncated_sub, anyMultiset: `pick_goal 3; rfl; simp` (coupled choice: True)
- sub_from_ten, any: `pick_goal 3; rfl; simp` (coupled choice: True)
- sub_from_ten, anyMultiset: `pick_goal 3; rfl; simp` (coupled choice: True)
- half_eight, any: `pick_goal 3; rfl; simp` (coupled choice: True)
- half_eight, anyMultiset: `pick_goal 3; rfl; simp` (coupled choice: True)
- cube_eight, any: `pick_goal 3; rfl; simp` (coupled choice: True)
- cube_eight, anyMultiset: `pick_goal 3; rfl; simp` (coupled choice: True)
- two_facts, firstText: `simp; simp`
- two_facts, first: `simp; simp` (coupled choice: False)
- two_facts, any: `simp; simp` (coupled choice: False)
- two_facts, anyMultiset: `simp; simp` (coupled choice: False)
- order_facts, firstText: `simp; simp`
- order_facts, first: `simp; simp` (coupled choice: False)
- order_facts, any: `simp; simp` (coupled choice: False)
- order_facts, anyMultiset: `simp; simp` (coupled choice: False)
- divisibility, firstText: `simp; simp`
- divisibility, first: `simp; simp` (coupled choice: False)
- divisibility, any: `simp; simp` (coupled choice: False)
- divisibility, anyMultiset: `simp; simp` (coupled choice: False)
- three_facts, firstText: `simp; simp; simp`
- three_facts, first: `simp; simp; simp` (coupled choice: False)
- three_facts, any: `simp; simp; simp` (coupled choice: False)
- three_facts, anyMultiset: `simp; simp; simp` (coupled choice: False)
- true_and_sum, firstText: `simp; simp`
- true_and_sum, first: `simp; simp` (coupled choice: False)
- true_and_sum, any: `simp; simp` (coupled choice: False)
- true_and_sum, anyMultiset: `simp; simp` (coupled choice: False)
- quotient_square, firstText: `simp; simp`
- quotient_square, first: `simp; simp` (coupled choice: False)
- quotient_square, any: `simp; simp` (coupled choice: False)
- quotient_square, anyMultiset: `simp; simp` (coupled choice: False)
- forall_first, firstText: `simp; simp`
- forall_first, first: `simp; simp` (coupled choice: False)
- forall_first, any: `simp; simp` (coupled choice: False)
- forall_first, anyMultiset: `simp; simp` (coupled choice: False)
- comm_first, firstText: `omega; simp`
- comm_first, first: `omega; simp` (coupled choice: False)
- comm_first, any: `omega; simp` (coupled choice: False)
- comm_first, anyMultiset: `omega; simp` (coupled choice: False)
