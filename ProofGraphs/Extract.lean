import Lean

/-!
# Goal-dependency graphs of tactic proofs

A tactic proof is elaborated with info trees enabled, and every leaf tactic
node that changes the goal list becomes a *step*: the goals it consumed
(present before, absent after) and the goals it produced (absent before,
present after). A step depends on the step that produced a goal it consumed.
The result, per declaration, is the list of steps with their producers; the
number of linear orderings of that dependency graph is the order redundancy
of the proof, counted downstream.
-/

open Lean Elab

namespace ProofGraphs

/-- One atomic tactic step. Goal ids are the `MVarId` names. -/
structure Step where
  syntaxKind : String
  consumed : Array String
  produced : Array String
  line : Nat
  deriving Repr

/-- All tactic steps of one declaration, in elaboration order. -/
structure ProofRecord where
  declaration : String
  module : String
  steps : Array Step
  deriving Repr

private def goalNames (goals : List MVarId) : Array String :=
  goals.toArray.map fun goal => goal.name.toString

/-- Leaf tactic nodes: tactic infos with no tactic info among their
descendants. Every node is visited with its context. -/
partial def leafTactics (tree : InfoTree) : Array (ContextInfo × TacticInfo) :=
  go tree none #[]
where
  hasTacticDescendant : InfoTree → Bool
    | .context _ t => hasTacticDescendant t
    | .node info children =>
        (match info with | .ofTacticInfo _ => true | _ => false) ||
          children.any hasTacticDescendant
    | .hole _ => false
  go (tree : InfoTree) (ctx? : Option ContextInfo) (acc : Array (ContextInfo × TacticInfo)) :
      Array (ContextInfo × TacticInfo) :=
    match tree with
    | .context part t => go t (part.mergeIntoOuter? ctx?) acc
    | .node info children =>
        let acc := match info, ctx? with
          | .ofTacticInfo tactic, some ctx =>
              if children.any hasTacticDescendant then acc else acc.push (ctx, tactic)
          | _, _ => acc
        children.foldl (fun acc child => go child ctx? acc) acc
    | .hole _ => acc

/-- Steps of a declaration from its leaf tactic nodes. A goal counts as consumed
by a node only when it is absent afterwards and never reappears in a later
node: focusing constructs such as `·` and `case` hide goals without closing
them. Nodes that neither consume nor produce a goal are not steps. -/
def stepsOf (leaves : Array (ContextInfo × TacticInfo)) : Array Step := Id.run do
  let mut steps : Array Step := #[]
  for ((ctx, tactic), index) in leaves.zipIdx do
    let before := goalNames tactic.goalsBefore
    let after := goalNames tactic.goalsAfter
    let laterBefore := (leaves.extract (index + 1) leaves.size).flatMap fun (_, later) =>
      goalNames later.goalsBefore
    let consumed := before.filter fun g => !after.contains g && !laterBefore.contains g
    let produced := after.filter fun g => !before.contains g
    if consumed.isEmpty && produced.isEmpty then
      continue
    let line := match tactic.stx.getPos? with
      | some pos => (ctx.fileMap.toPosition pos).line
      | none => 0
    steps := steps.push { syntaxKind := tactic.stx.getKind.toString, consumed, produced, line }
  return steps

/-- Elaborates one Lean source file with info trees enabled and returns the
tactic steps of every declaration that has any. -/
def processFile (module : String) (path : System.FilePath) : IO (Array ProofRecord × String) := do
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let options := Options.empty.setBool `Elab.async false
  let (env, messages) ← processHeader header options messages inputCtx
  let headerErrors := messages.toList.filter (·.severity == .error)
  let commandState := { Command.mkState env messages options with
    infoState := { enabled := true, trees := {} } }
  let result ← IO.processCommands inputCtx parserState commandState
  let trees := result.commandState.infoState.trees.toArray
  let mut byDeclaration : Std.HashMap String (Array (ContextInfo × TacticInfo)) := {}
  let mut order : Array String := #[]
  for tree in trees do
    for (ctx, tactic) in leafTactics tree do
      let name := match ctx.parentDecl? with
        | some declaration => declaration.toString
        | none => "<anonymous>"
      if !byDeclaration.contains name then
        order := order.push name
      byDeclaration := byDeclaration.insert name ((byDeclaration.getD name #[]).push (ctx, tactic))
  let mut records : Array ProofRecord := #[]
  for name in order do
    let steps := stepsOf (byDeclaration.getD name #[])
    if !steps.isEmpty then
      records := records.push { declaration := name, module, steps }
  let errors := headerErrors ++ result.commandState.messages.toList.filter (·.severity == .error)
  let mut rendered := ""
  for error in errors.take 3 do
    rendered := rendered ++ " | " ++ (← error.toString)
  let diagnostics := s!"modules={env.header.moduleNames.size} trees={trees.size} declarations={order.size} errors={errors.length}{rendered}"
  return (records, diagnostics)

def Step.toJson (step : Step) : Json :=
  Json.mkObj [
    ("kind", step.syntaxKind),
    ("consumed", Json.arr (step.consumed.map Json.str)),
    ("produced", Json.arr (step.produced.map Json.str)),
    ("line", step.line)]

def ProofRecord.toJson (record : ProofRecord) : Json :=
  Json.mkObj [
    ("declaration", record.declaration),
    ("module", record.module),
    ("steps", Json.arr (record.steps.map Step.toJson))]

end ProofGraphs
