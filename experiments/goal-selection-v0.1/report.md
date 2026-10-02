# Goal-selection search v0.1

Candidate tasks: 1347; budget: 24 expansions, or 7200 search seconds in typed arms.

| Arm | Posed | Completed | Proved | Expansions | Steps | Text order fraction | Typed order fraction |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| firstText | 200 | 200 | 103 | 1632 | 40688 | 0.0428921568627451 | None |
| first | 1171 | 1171 | 103 | 15831 | 409860 | 0.041374518350072644 | 0.04450212065582072 |
| any | 1171 | 1171 | 98 | 16851 | 770864 | 0.07340810634383717 | 0.07667200759598837 |
| anyMultiset | 1171 | 1171 | 98 | 16649 | 739378 | 0.006006366748753679 | 0.0 |

Typed fractions use exported support; unknown keys do not count as nonduplicates.
Distinct typed multisets are summed within searches, whose task environments differ.
Pairwise comparisons use tasks with completed results in both arms.
At equal steps every arm's proof must close within 624 candidate applications.
Wall-clock stops remain paired; abandoned units are excluded and become final after two abandonments.

## Decisions

| Item | Result |
| --- | --- |
| H78 | fails, p = 0.03125 |
| H80 | fails, p = None |
| H81 | holds, p = 9.999000099990002e-05 |
| H79 | untested |
| C1 | holds |
| C2 | holds |
| C3 | holds |

## Measures and paired comparisons

```json
{
 "arms": {
  "firstText": {
   "tasksPosed": 200,
   "completed": 200,
   "missing": 0,
   "errors": 0,
   "abandoned": 0,
   "finalAbandoned": 0,
   "wallClockStops": 0,
   "proved": 103,
   "expansions": 1632,
   "steps": 40688,
   "validChildren": 5885,
   "orderDuplicates": 70,
   "orderFraction": 0.0428921568627451,
   "typedOrderDuplicates": 0,
   "typedOrderSupport": 0,
   "typedOrderFraction": null,
   "exactDuplicates": 3301,
   "exactFraction": 0.5609175870858114,
   "multisetDuplicates": null,
   "multisetFraction": null,
   "distinctTypedMultisets": null,
   "coupledMultiGoalStates": 0,
   "exportedMultiGoalStates": 0,
   "coupledFraction": null,
   "exportFailures": 0,
   "exportAttempts": 0
  },
  "first": {
   "tasksPosed": 1171,
   "completed": 1171,
   "missing": 0,
   "errors": 0,
   "abandoned": 0,
   "finalAbandoned": 0,
   "wallClockStops": 0,
   "proved": 103,
   "expansions": 15831,
   "steps": 409860,
   "validChildren": 62712,
   "orderDuplicates": 655,
   "orderFraction": 0.041374518350072644,
   "typedOrderDuplicates": 703,
   "typedOrderSupport": 15797,
   "typedOrderFraction": 0.04450212065582072,
   "exactDuplicates": 39817,
   "exactFraction": 0.6349183569332824,
   "multisetDuplicates": 40985,
   "multisetFraction": 0.6535431815282562,
   "distinctTypedMultisets": 15094,
   "coupledMultiGoalStates": 2106,
   "exportedMultiGoalStates": 7433,
   "coupledFraction": 0.2833310910803175,
   "exportFailures": 0,
   "exportAttempts": 63883
  },
  "any": {
   "tasksPosed": 1171,
   "completed": 1171,
   "missing": 0,
   "errors": 0,
   "abandoned": 0,
   "finalAbandoned": 0,
   "wallClockStops": 0,
   "proved": 98,
   "expansions": 16851,
   "steps": 770864,
   "validChildren": 114012,
   "orderDuplicates": 1237,
   "orderFraction": 0.07340810634383717,
   "typedOrderDuplicates": 1292,
   "typedOrderSupport": 16851,
   "typedOrderFraction": 0.07667200759598837,
   "exactDuplicates": 64166,
   "exactFraction": 0.5628004069747045,
   "multisetDuplicates": 77430,
   "multisetFraction": 0.6791390379960004,
   "distinctTypedMultisets": 15559,
   "coupledMultiGoalStates": 2545,
   "exportedMultiGoalStates": 8434,
   "coupledFraction": 0.3017548019919374,
   "exportFailures": 0,
   "exportAttempts": 115183
  },
  "anyMultiset": {
   "tasksPosed": 1171,
   "completed": 1171,
   "missing": 0,
   "errors": 0,
   "abandoned": 0,
   "finalAbandoned": 0,
   "wallClockStops": 0,
   "proved": 98,
   "expansions": 16649,
   "steps": 739378,
   "validChildren": 111963,
   "orderDuplicates": 100,
   "orderFraction": 0.006006366748753679,
   "typedOrderDuplicates": 0,
   "typedOrderSupport": 16649,
   "typedOrderFraction": 0.0,
   "exactDuplicates": 60421,
   "exactFraction": 0.5396514920107536,
   "multisetDuplicates": 72918,
   "multisetFraction": 0.6512687227030358,
   "distinctTypedMultisets": 16649,
   "coupledMultiGoalStates": 2448,
   "exportedMultiGoalStates": 8123,
   "coupledFraction": 0.3013664902129755,
   "exportFailures": 0,
   "exportAttempts": 113134
  }
 },
 "pairs": {
  "firstText:first": {
   "pairedCompleted": 200,
   "equalExpansions": {
    "aOnly": 1,
    "bOnly": 0,
    "pAGreater": 0.5,
    "pBGreater": 1.0
   },
   "equalSteps": {
    "aOnly": 1,
    "bOnly": 0,
    "pAGreater": 0.5,
    "pBGreater": 1.0
   }
  },
  "first:any": {
   "pairedCompleted": 1171,
   "equalExpansions": {
    "aOnly": 5,
    "bOnly": 0,
    "pAGreater": 0.03125,
    "pBGreater": 1.0
   },
   "equalSteps": {
    "aOnly": 5,
    "bOnly": 0,
    "pAGreater": 0.03125,
    "pBGreater": 1.0
   }
  },
  "any:anyMultiset": {
   "pairedCompleted": 1171,
   "equalExpansions": {
    "aOnly": 0,
    "bOnly": 0,
    "pAGreater": null,
    "pBGreater": null
   },
   "equalSteps": {
    "aOnly": 0,
    "bOnly": 0,
    "pAGreater": null,
    "pBGreater": null
   }
  },
  "first:anyMultiset": {
   "pairedCompleted": 1171,
   "equalExpansions": {
    "aOnly": 5,
    "bOnly": 0,
    "pAGreater": 0.03125,
    "pBGreater": 1.0
   },
   "equalSteps": {
    "aOnly": 5,
    "bOnly": 0,
    "pAGreater": 0.03125,
    "pBGreater": 1.0
   }
  }
 },
 "hypotheses": {
  "H78": {
   "firstOnly": 5,
   "anyOnly": 0,
   "p": 0.03125,
   "holds": false
  },
  "H79": {
   "status": "untested",
   "cases": []
  },
  "H80": {
   "anyOnly": 0,
   "anyMultisetOnly": 0,
   "p": null,
   "holds": false
  },
  "H81": {
   "tasks": 1171,
   "difference": 0.03216988694016765,
   "interval": [
    0.026036425909010195,
    0.03854400899738432
   ],
   "p": 9.999000099990002e-05,
   "holds": true
  }
 },
 "checks": {
  "C2": {
   "typedOrderDuplicates": 0,
   "holds": true
  },
  "C3": {
   "exportFailures": 0,
   "exportAttempts": 292200,
   "share": 0.0,
   "holds": true
  }
 },
 "C1": {
  "compared": 200,
  "matched": 200,
  "mismatches": [],
  "sampleMatches": true,
  "holds": true
 }
}
```

## Free-choice-only proofs

