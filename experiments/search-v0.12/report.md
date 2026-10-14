# The independent-goal search on search-v0.11's held-out tasks (search v0.12)

Tasks: 591; stated: 591. Proved: {'goals': {'24': 142, '48': 154}, 'whole': {'24': 133, '48': 147}, 'groups': {'24': 140, '48': 153}}.

- groupsOverGoals: cells {'both': 153, 'firstOnly': 0, 'secondOnly': 1, 'neither': 437}; difference -0.001692047377326565; Newcombe 95% [-0.006273944338338351, 0.002789529614228144]; module interval [-0.005629, 0.0]; one-sided sign test 1.0.
- goalsOverWhole: cells {'both': 146, 'firstOnly': 8, 'secondOnly': 1, 'neither': 436}; difference 0.011844331641285956; Newcombe 95% [0.0016275048656555404, 0.02235952419779262]; module interval [0.00318, 0.021898]; one-sided sign test 0.01953125.
- groupsOverWhole: cells {'both': 146, 'firstOnly': 7, 'secondOnly': 1, 'neither': 437}; difference 0.01015228426395939; Newcombe 95% [0.00044865549155779887, 0.020130234141936272]; module interval [0.001698, 0.019108]; one-sided sign test 0.03515625.

## Hypotheses

- H112 (holds): the coupled-group search (search-v0.11's rows) does not prove significantly more tasks than the independent-goal search within 48 expansions (one-sided sign test on the tasks exactly one of them proves, Holm's procedure at 0.05 over this test and H113's).
- H113 (holds): the independent-goal search proves significantly more tasks than the whole-state search (search-v0.11's rows) within 48 expansions (one-sided sign test on the tasks exactly one of them proves, Holm's procedure at 0.05 over this test and H112's).
- H114 (holds): the upper limit of the 95% interval (Newcombe's hybrid score interval for paired proportions) for the group search's proof rate minus the independent-goal search's is below 1 point, about the gain search-v0.11 estimated for the group search over the whole-state search.

## Checks

- C45 (holds): every unit is final, and no latest row records an error.
- C46 (holds): the typed export fails on fewer than 1% of the states the search exports.
- C47 (holds): every candidate set the search takes as seeded is one search-v0.11 recorded, or an earlier attempt of the unit drew, for that goal and occurrence in the task.
