import Lean

/-!
# Goal-dependency graphs of tactic proofs

A tactic proof is elaborated with info trees enabled, and every tactic info
node is recorded with its goals before and after, its parent node, and
whether it is a leaf. The step-dependency graph is derived downstream
(`scripts/count_linearizations.py`): leaf nodes that change the goal list are
steps, and a structured node such as `induction ... with` whose case goals
are consumed only by its descendants is a step producing those goals.
-/

open Lean Elab

namespace ProofGraphs

/-- One tactic info node. `parent` is the index of the nearest enclosing
tactic node in the same declaration, or `none`; `leaf` says whether no tactic
node lies below it. Goal ids are the `MVarId` names. -/
structure Node where
  index : Nat
  parent : Option Nat
  leaf : Bool
  syntaxKind : String
  before : Array String
  after : Array String
  line : Nat
  deriving Repr, Inhabited

/-- All tactic nodes of one declaration, in tree order. -/
structure ProofRecord where
  declaration : String
  module : String
  nodes : Array Node
  deriving Repr

private def goalNames (goals : List MVarId) : Array String :=
  goals.toArray.map fun goal => goal.name.toString

/-- Every tactic node with its context, parent index, and leaf flag, in tree
order; the declaration name comes from the context. -/
partial def tacticNodes (tree : InfoTree) : Array (Option Name × Node) :=
  (go tree none none #[]).1
where
  hasTacticDescendant : InfoTree → Bool
    | .context _ t => hasTacticDescendant t
    | .node info children =>
        (match info with | .ofTacticInfo _ => true | _ => false) ||
          children.any hasTacticDescendant
    | .hole _ => false
  go (tree : InfoTree) (ctx? : Option ContextInfo) (parent : Option Nat)
      (acc : Array (Option Name × Node)) : Array (Option Name × Node) × Option Nat :=
    match tree with
    | .context part t => go t (part.mergeIntoOuter? ctx?) parent acc
    | .node info children =>
        match info, ctx? with
        | .ofTacticInfo tactic, some ctx =>
            let index := acc.size
            let line := match tactic.stx.getPos? with
              | some pos => (ctx.fileMap.toPosition pos).line
              | none => 0
            let node : Node := {
              index, parent, leaf := !children.any hasTacticDescendant,
              syntaxKind := tactic.stx.getKind.toString,
              before := goalNames tactic.goalsBefore, after := goalNames tactic.goalsAfter, line }
            let acc := acc.push (ctx.parentDecl?, node)
            (children.foldl (fun acc child => (go child ctx? (some index) acc).1) acc, some index)
        | _, _ =>
            (children.foldl (fun acc child => (go child ctx? parent acc).1) acc, parent)
    | .hole _ => (acc, parent)

/-- Elaborates one Lean source file with info trees enabled and returns the
tactic nodes of every declaration that has any. The declarations elaborated
by one command (a theorem and its `@[ext]` companions, derived instances,
every `example` of the file) share one info tree and one index space; their
nodes are split per declaration and re-indexed, a parent outside the
declaration becoming `none`. Private declarations carry their user-facing
name, and a name that repeats within the file is suffixed with the line of
its first node. -/
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
  let mut records : Array ProofRecord := #[]
  let mut used : Std.HashSet String := {}
  for tree in trees do
    let mut byDeclaration : Std.HashMap String (Array Node) := {}
    let mut order : Array String := #[]
    for (declaration?, node) in tacticNodes tree do
      let name := match declaration? with
        | some declaration => ((privateToUserName? declaration).getD declaration).toString
        | none => "<anonymous>"
      if !byDeclaration.contains name then
        order := order.push name
      byDeclaration := byDeclaration.insert name ((byDeclaration.getD name #[]).push node)
    for name in order do
      let group := byDeclaration.getD name #[]
      let mut remap : Std.HashMap Nat Nat := {}
      for h : i in [0:group.size] do
        remap := remap.insert group[i].index i
      let nodes := group.mapIdx fun i node =>
        { node with index := i, parent := node.parent.bind fun p => remap.get? p }
      let declaration := if used.contains name then s!"{name}:L{(group[0]!).line}" else name
      used := used.insert declaration
      if !nodes.isEmpty then
        records := records.push { declaration, module, nodes }
  let errors := headerErrors ++ result.commandState.messages.toList.filter (·.severity == .error)
  let mut rendered := ""
  for error in errors.take 3 do
    rendered := rendered ++ " | " ++ (← error.toString)
  let diagnostics := s!"modules={env.header.moduleNames.size} trees={trees.size} declarations={records.size} errors={errors.length}{rendered}"
  return (records, diagnostics)

def Node.toJson (node : Node) : Json :=
  Json.mkObj [
    ("index", node.index),
    ("parent", match node.parent with | some p => Json.num p | none => Json.null),
    ("leaf", node.leaf),
    ("kind", node.syntaxKind),
    ("before", Json.arr (node.before.map Json.str)),
    ("after", Json.arr (node.after.map Json.str)),
    ("line", node.line)]

def ProofRecord.toJson (record : ProofRecord) : Json :=
  Json.mkObj [
    ("declaration", record.declaration),
    ("module", record.module),
    ("nodes", Json.arr (record.nodes.map Node.toJson))]

end ProofGraphs
