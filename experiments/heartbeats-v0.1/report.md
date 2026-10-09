# heartbeats-v0.1

Units: 2694; tasks posed in both experiments: 1170; errors 0, abandoned 0.

- whole: 102 proved under the limit against 102 in search-v0.3; lost 0, gained 0.
- andor: 102 proved under the limit against 102 in search-v0.3; lost 0, gained 0.

AND-OR only 2, whole-state only 2, two-sided p 1.0.
Applications stopped on the limit: 2650.

## Hypotheses

- H100 (holds): each search proves at least 95% as many tasks under the limit as it proved in search-v0.3.
- H101 (holds): under the limit, the AND-OR and whole-state searches do not differ significantly: a two-sided sign test on the tasks exactly one of them proves gives p >= 0.05, as in search-v0.3.
- H102 (holds): under the limit, the whole-state search's order-duplicate fraction is below 5% and its goal-duplicate fraction at least twice its order-duplicate fraction, as search-v0.3's H22 and H23 found.

## Checks

- C38 (holds): every unit whose module session was set up defined the limiting tactic.
- C39 (holds): the limit is reached: at least one candidate application stops on the heartbeat limit.
