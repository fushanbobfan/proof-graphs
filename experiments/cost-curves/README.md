# Cost curves (exploratory, not registered)

The search experiments count their budgets in expansions, and an expansion of one design can apply more candidate
tactics than an expansion of another: a free-choice expansion applies every candidate to every open goal, and the goal
and group searches expand a merged goal once where the whole-state search expands it in every state that carries it.
`scripts/explore_cost_curves.py` reads the committed rows of search-v0.3, goal-selection-v0.1, search-v0.8,
search-v0.9, and, once their runs are complete, search-v0.10 and v0.11, and gives, per search and set of draws, how
many tasks are proved within a per-task budget of candidate
applications (16 to 16,384). A search's applications at its proof are those of the expansions up to and including the
one that found it; goal-selection-v0.1 records the exact count.

```text
python scripts/explore_cost_curves.py --check
```

recomputes `summary.json` from the committed rows; CI runs it.

The curves count every unit a search constructed, not only the tasks stated in all searches of an experiment, so
their totals can differ slightly from the paper's. Each curve ends where its search's own expansion budget did: two
designs are compared at equal work only below the smaller of their final points. Model draws are not counted: in the
step-prover experiments each expansion uses one draw, so draws equal expansions.
