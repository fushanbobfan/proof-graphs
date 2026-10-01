# Keys v0.1: matched-support denominators

Exploratory audit of committed v1 expression-key digests. No v2 keys are recomputed.

Both goal-duplicate histories use only expansions whose state exported. Each history starts empty in each unit; only its first goal is counted. Shares divide by evaluable expansions.

| Arm | Logged / total units | Expansion total | Evaluable | Missing | Expression duplicates / share | Coarse duplicates / share |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| proverWhole | 168 / 200 | 4703 | 4607 | 96 | 1277 / 27.7187% | 1192 / 25.8737% |
| proverWholeRenamed | 169 / 200 | 4358 | 4262 | 96 | 359 / 8.4233% | 247 / 5.7954% |
| proverAndor | 168 / 200 | 4855 | 4759 | 96 | 1151 / 24.1858% | 1073 / 22.5468% |
| proverAndorRenamed | 169 / 200 | 4512 | 4416 | 96 | 150 / 3.3967% | 37 / 0.8379% |
| menuWhole | 258 / 300 | 3417 | 3374 | 43 | 974 / 28.8678% | 946 / 28.0379% |

False identifications keep the original search's text-key history, including entries that did not export. A comparison is missing if either endpoint lacks an expression key. Shares divide by evaluable comparisons; missing comparisons are never counted as correct.

| Arm / decision | Total | Evaluable | Missing | False | False / evaluable |
| --- | ---: | ---: | ---: | ---: | ---: |
| proverWhole / falseDrops | 2905 | 2862 | 43 | 170 | 5.9399% |
| proverWholeRenamed / falseDrops | 4335 | 4240 | 95 | 214 | 5.0472% |
| proverAndor / falseMerges | 2809 | 2739 | 70 | 244 | 8.9084% |
| proverAndorRenamed / merges | unknown | unknown | unknown | unknown | unavailable |
| menuWhole / falseDrops | 7009 | 6891 | 118 | 410 | 5.9498% |
| Pooled whole-state drops | 14249 | 13993 | 256 | 794 | 5.6743% |

Observed expansions in logged units; histories reset for each unit. Unlogged units' expansions and decisions are unknown, not zero.

## Data limits

- Only v1 key digests are recorded; instantiated expression trees needed to recompute v2 keys and corrected unordered state identity are absent.
- Renamed AND-OR merge decisions, alias-to-node mappings, accepted renaming targets, and goal text for rebuilding renaming_step/agrees are absent. Its false-merge counts and share cannot be recovered; coarse-key equality alone is not an accepted merge.

Source SHA-256 digests are in summary.json; they cover logs.jsonl.gz, results.jsonl, and summary.json read with git show HEAD. The logs/results digests are checked against the source summary, with mismatches reported below. Reconstructed drops and printed AND-OR merges match committed per-unit counts. The root is excluded from printed AND-OR arrivals, as in the original audit.

## Source integrity

- logs.jsonl.gz: SHA-256 mismatch. Source summary records `b9b60174d1e500fb3fb2978eabf80857ea93ff348cd314d94cce45ac76b77603`; the committed blob is `70de16d1f5003a562a79a8a65d45226d5b199f851d429c9a73318d2c26d9590c`. This audit uses the committed blob and verifies gzip decoding, unit coverage, and per-unit decision counts. The digest discrepancy's cause cannot be established from these three artifacts.
- results.jsonl: SHA-256 matches the source summary.

```text
python scripts/audit_key_denominators.py --check
```
