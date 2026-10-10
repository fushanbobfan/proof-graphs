# Searches with the typed key (search v0.10)

Frozen in `preregistration.json` (SHA-256 `39624a8b1caca3321106ef358daf71610e20e904a692316b3cd573f065430e39`).

Tasks: 200; stated in all nine searches: 169; unit attempts: 728.

| Search | set 0 | set 1 | set 2 | (48 expansions) |
|---|---:|---:|---:|---|
| whole | 41 | 39 | 43 | |
| goals | 43 | 42 | 44 | |
| groups | 43 | 42 | 45 | |

At 256 expansions in set 0: {'whole': {48: 41, 96: 44, 192: 46, 256: 46}, 'groups': {48: 43, 96: 46, 192: 47, 256: 48}}; groups only 3, whole only 1, one-sided p 0.3125.

Audit of the expression key: drops {'agree': 79546, 'typedOnly': 16, 'expressionOnly': 157, 'unexported': 0, 'agreement': 0.9978298774445239}; merges {'agree': 124376, 'typedOnly': 37, 'expressionOnly': 390, 'unexported': 0, 'agreement': 0.9965786078860284}.

## Hypotheses

- H103 (holds): at 48 expansions over the three sets of draws, no comparison of two searches is significant after Holm's adjustment (one-sided sign tests on the tasks whose scores, the sets in which a search proves the task, differ, as registered in search-v0.8), as in search-v0.8.
- H104 (holds): at 256 expansions in the first set, the group search does not prove significantly more than the whole-state search (one-sided sign test, p >= 0.05), as in search-v0.9.
- H105 (holds): where both keys exported, the typed and expression keys agree on at least 99% of the whole-state searches' decisions whether a generated state had been generated before.
- H106 (holds): in every set, each search proves within 2 tasks of what it proved with the expression key at the same budget (search-v0.8 at 48 expansions, search-v0.9 at 256).

## Checks

- C40 (holds): every unit is final, and no latest row records an error.
- C41 (holds): the typed export fails on fewer than 1% of the states the searches export.
