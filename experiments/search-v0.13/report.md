# Two new sets of draws for the three searches on the held-out tasks (search v0.13)

Tasks: 591; stated in all six searches: 591. Proved: {'whole': {'1': {'24': 128, '48': 143}, '2': {'24': 128, '48': 143}}, 'goals': {'1': {'24': 133, '48': 140}, '2': {'24': 131, '48': 146}}, 'groups': {'1': {'24': 132, '48': 140}, '2': {'24': 131, '48': 145}}}.

- groupsOverWhole: tasks first more 8, second more 11; one-sided sign test 0.8203582763671875; mean difference -0.0008460236886632825; module interval [-0.007614, 0.006108].
- groupsOverGoals: tasks first more 2, second more 2; one-sided sign test 0.6875; mean difference -0.0008460236886632825; module interval [-0.005566, 0.00318].
- goalsOverWhole: tasks first more 8, second more 9; one-sided sign test 0.6854705810546875; mean difference 0.0; module interval [-0.007282, 0.00738].

## Hypotheses

- H115 (fails): over the two new sets, the group search's score (the sets in which it proves the task within 48 expansions) exceeds the whole-state search's on significantly more tasks than the reverse (one-sided sign test at 0.05 on the tasks whose scores differ).
- H116 (holds): the upper limit of the 95% interval, resampling modules, for the group search's proof rate minus the whole-state search's over the two new sets is below 3 points.
- H117 (holds): the group search's score does not exceed the independent-goal search's on significantly more tasks than the reverse (one-sided sign test on the tasks whose scores differ, Holm's procedure at 0.05 over this test and H118's).
- H118 (fails): the independent-goal search's score exceeds the whole-state search's on significantly more tasks than the reverse (one-sided sign test on the tasks whose scores differ, Holm's procedure at 0.05 over this test and H117's).

## Checks

- C48 (holds): every unit is final, and no latest row records an error.
- C49 (holds): the typed export fails on fewer than 1% of the states the searches export.
- C50 (holds): no candidate set is drawn twice for the same goal and occurrence in a unit, and every set a search takes as seeded is one an earlier attempt of the unit drew.
