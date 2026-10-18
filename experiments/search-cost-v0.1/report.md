# What each search costs, run alone with its own draws (search-cost v0.1)

Tasks: 30.

- whole: {"searches": 30, "proved": 8, "abandoned": 0, "medianElapsedSeconds": 128.62, "medianPeakMemoryMB": 4038.8500000000004, "totals": {"elapsedSeconds": 6310.4, "modelRequests": 716, "completionTokens": 173537, "promptTokens": 1714544, "modelSeconds": 3989.2, "tacticSeconds": 661.3, "exportSeconds": 203.9, "commandSeconds": 1012.5, "tacticCalls": 8667, "exportCalls": 4064}, "modelLargestShareOfTasks": 0.5333333333333333, "medianExportShare": 0.007103774478658596}
- goals: {"searches": 30, "proved": 9, "abandoned": 0, "medianElapsedSeconds": 237.59, "medianPeakMemoryMB": 4226.15, "totals": {"elapsedSeconds": 8011.9, "modelRequests": 874, "completionTokens": 222827, "promptTokens": 2062816, "modelSeconds": 5320.8, "tacticSeconds": 673.6, "exportSeconds": 328.5, "commandSeconds": 1029.8, "tacticCalls": 10842, "exportCalls": 5202}, "modelLargestShareOfTasks": 0.6666666666666666, "medianExportShare": 0.011634142049124642}
- groups: {"searches": 30, "proved": 5, "abandoned": 0, "medianElapsedSeconds": 252.885, "medianPeakMemoryMB": 4084.8500000000004, "totals": {"elapsedSeconds": 8106.2, "modelRequests": 929, "completionTokens": 221277, "promptTokens": 1969360, "modelSeconds": 5343.8, "tacticSeconds": 945.2, "exportSeconds": 249.0, "commandSeconds": 982.5, "tacticCalls": 11076, "exportCalls": 5662}, "modelLargestShareOfTasks": 0.7, "medianExportShare": 0.011444671786451154}

Ratios: {"goalsOverWhole": {"tasks": 30, "median": 1.1026543283195842, "interval95": [1.069986259633192, 1.163119860453526]}, "groupsOverWhole": {"tasks": 30, "median": 1.2139258441671008, "interval95": [1.1191344720321474, 1.50496149849221]}}

## Hypotheses

- H122 (holds): in each search, the model's time is the largest of the recorded components of elapsed time (model draws, candidate tactics, exports, setup and verification commands) in more than half of the tasks.
- H123 (holds): the median over tasks of the group search's elapsed time divided by the whole-state search's lies between 0.8 and 1.25.
- H124 (holds): in the independent-goal and group searches, the exports that decide identity take less than a fifth of the elapsed time in the median task.

## Checks

- C53 (holds): every search of every sampled task runs to an outcome (a proof, an exhausted frontier, the budget, or an abandoned session), and none raises.
- C54 (holds): no other search experiment's runner runs while a search of this one does.
