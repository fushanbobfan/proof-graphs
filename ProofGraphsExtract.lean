import ProofGraphs

open Lean

/-- `proof_graph_extract <module-name> <file> ...` prints one JSON line per
declaration with tactic steps, for each `<module-name> <file>` pair. -/
unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let rec loop : List String → IO Unit
    | module :: file :: rest => do
        let (records, diagnostics) ← ProofGraphs.processFile module file
        IO.eprintln s!"{module}: {diagnostics}"
        for record in records do
          IO.println record.toJson.compress
        loop rest
    | [] => pure ()
    | [_] => throw <| IO.userError "expected <module> <file> pairs"
  loop args
