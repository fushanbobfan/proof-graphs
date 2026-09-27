# A reconstruction kit for people

The same task as the model reconstructors of this audit, for a person: `../instructions.md` is the
definition and the rules, and `worksheet.md` lists the proofs with their source. Fill in one JSON
entry per proof as the instructions show and save them as a list in `reconstructions-by-hand.json`;
`python scripts/run_extraction_audit_v2.py --compare-hand` then compares them with the derived graphs
without showing those graphs first. Displaying Lean's goals at a line (in an editor with the Lean
extension, opening the source file in this repository's Lean project) is allowed and expected.
