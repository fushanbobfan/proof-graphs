# Whole states and coupled goal groups on held-out theorems (search v0.11)

Tasks: 720; stated in both searches: 591.

Proved: {'whole': {'24': 133, '48': 147}, 'groups': {'24': 140, '48': 153}}; cells {'both': 146, 'groupsOnly': 7, 'wholeOnly': 1, 'neither': 437}; difference 0.01015228426395939; Newcombe 95% [0.00044865549155779887, 0.020130234141936272]; module interval [0.001667, 0.018762]; one-sided sign test 0.03515625.

## Hypotheses

- H109 (fails): the group search does not prove significantly more tasks than the whole-state search (one-sided sign test on the tasks exactly one of them proves, p >= 0.05).
- H110 (holds): the upper limit of the 95% interval (Newcombe's hybrid score interval for paired proportions) for the group search's proof rate minus the whole-state search's is below 3 points.
- H111 (holds): goal duplicates under the typed key are below 10% of the whole-state search's expansions.

## Checks

- C43 (holds): every unit is final, and no latest row records an error.
- C44 (holds): the typed export fails on fewer than 1% of the states the searches export.
