# Agent notes

Start with [HANDOFF.md](HANDOFF.md): the state, what is claimed, how each
claim is re-verified, and where a cross-check is most valuable. The research
object and the answer are in [docs/design.md](docs/design.md).

- The extractor (`ProofGraphs/Extract.lean`, `ProofGraphsExtract.lean`), the
  counter (`scripts/count_linearizations.py`), the search harness
  (`scripts/search_harness.py`, `scripts/lean_repl.py`), the golf miner, and
  every runner are hashed by the preregistrations. Changing one makes the
  committed checks fail until an `amendment-N.json` records the change; see
  the existing amendments for the format. New work goes in new files or a
  new experiment directory.
- Never edit a `preregistration.json`. Register a new experiment with its
  runner's `--register` and push the registration before any run.
- Before pushing, run the `--check-committed` of every experiment whose
  inputs you touched, and `python scripts/export_graphs.py --check`.
- Text files are LF (`.gitattributes`). A Windows checkout of Mathlib may be
  CRLF; read module text with `git show`, as `scripts/run_golf.py` does.
- History is never rewritten. Commit subjects state the change in one line,
  with no tool or assistant attribution.
