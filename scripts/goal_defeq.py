#!/usr/bin/env python3
"""Goal identity up to definitional equality, in the manner of Lean's canonicalizer.

The faithful key of `goal_identity` is syntactic: two goals whose Lean expressions differ only by an instance path, a
universe level written differently, or an unreduced lambda count as different, although they are likely
definitionally equal. Testing every pair with `isDefEq` is too costly. Lean's `Meta.Canonicalizer` instead hashes a
term while ignoring its implicit arguments, its proof arguments and the universe levels of its constants, and tests
`isDefEq` only between terms with equal hashes. That module is not imported by every Mathlib module, and a REPL cannot
import it into a task's environment, so `DEFEQ_TEMPLATE` implements the same procedure.

A goal is compared as its closed type, its local context abstracted over its target (`mkForallFVars`, implementation
details skipped), so that goals from different proof states of one search can meet in one context. Two `run_tac`
blocks do the work:

- `CLOSED_TACTIC`, in a proof state: for each goal, the closed type printed with `pp.all` (binder names replaced by
  `x0`, `x1`, ... so that no inaccessible name is printed), its universe parameters, and whether the printed text
  elaborates back, in the same state, to the same expression (`exact`), to one equal up to reducible unfolding
  (`reducible`), or not (`differs`, or an error); a goal whose closed type has a metavariable is marked and not
  printed, since a metavariable cannot be carried to another context;
- `defeq_tactic(path)`, in a proof state of the same environment: reads the printed types of a unit's distinct goals
  from a JSON file and elaborates each; beta-reduces it and normalizes its universe levels, which preserve definitional
  equality at every transparency; hashes it as the canonicalizer does, together with its number of hypotheses, since
  `h : P ⊢ Q` and `⊢ P → Q` share a closed type but are different goals; and then, in order, merges each goal into the
  first earlier goal with the same hash that `isDefEq` accepts, at reducible and at instances transparency. Each
  `isDefEq` runs with its own heartbeat budget (the `maxHeartbeats` the block runs under); one that exhausts it counts
  as not equal and is reported. For each goal it returns the index of the first goal of its class, and the time of
  each goal's elaboration and merge.
"""

from __future__ import annotations

import json
from typing import Any

from lean_repl import LeanRepl, ReplTimeout

HEARTBEATS = 400000
DEFEQ_HEARTBEATS = 200000
# Printing every implicit argument, universe and coercion, raw literals as `nat_lit`, and full names, so that the
# text names the expression rather than an elaboration of it.
PP_OPTIONS = ("o.setBool `pp.all true |>.setBool `pp.natLit true |>.setBool `pp.fullNames true "
              "|>.setBool `pp.proofs true |>.setBool `pp.mvars true")

CLOSED_TACTIC = r"""run_tac do
  let mut out : Array Lean.Json := #[]
  for g in (← Lean.Elab.Tactic.getGoals) do
    let r ← g.withContext do
      let decl ← g.getDecl
      let mut fvars : Array Lean.Expr := #[]
      for d? in decl.lctx.decls.toArray do
        if let some d := d? then
          if !d.isImplementationDetail then
            fvars := fvars.push d.toExpr
      let t0 ← Lean.instantiateMVars (← Lean.Meta.mkForallFVars fvars decl.type)
      if t0.hasMVar then
        return Lean.Json.mkObj [("mvar", true)]
      let counter ← IO.mkRef (0 : Nat)
      let t ← Lean.Core.transform t0 (post := fun e => do
        match e with
        | .forallE _ d b bi =>
          let n ← counter.modifyGet fun c => (c, c + 1)
          return .done (.forallE (Lean.Name.mkSimple s!"x{n}") d b bi)
        | .lam _ d b bi =>
          let n ← counter.modifyGet fun c => (c, c + 1)
          return .done (.lam (Lean.Name.mkSimple s!"x{n}") d b bi)
        | _ => return .continue)
      let levels := (Lean.collectLevelParams {} t).params
      let fmt ← Lean.withOptions (fun o => PP_OPTIONS) (Lean.Meta.ppExpr t)
      let s := fmt.pretty 1000000
      let rt ← try
          let stx ← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `term s)
          let t' ← Lean.Elab.Term.withLevelNames levels.toList do
            Lean.Elab.Term.withoutErrToSorry do
              let e ← Lean.Elab.Term.elabTerm stx none
              Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
              Lean.instantiateMVars e
          if t' == t then pure "exact"
          else if (← Lean.Meta.withReducible (Lean.Meta.isDefEq t' t)) then pure "reducible"
          else pure "differs"
        catch ex => pure s!"error: {← ex.toMessageData.toString}"
      return Lean.Json.mkObj [("pp", s), ("rt", rt), ("levels", Lean.toJson (levels.map toString)),
        ("hyps", Lean.toJson fvars.size)]
    out := out.push r
  Lean.logInfo (Lean.Json.arr out).compress""".replace("PP_OPTIONS", PP_OPTIONS)

DEFEQ_TEMPLATE = r"""run_tac do
  let text ← IO.FS.readFile PATH
  let entries ← Lean.ofExcept (Lean.Json.parse text >>= fun j => j.getArr?)
  let normalize : Lean.Expr → Lean.MetaM Lean.Expr := fun e => do
    let e ← Lean.Core.betaReduce e
    Lean.Core.transform e (post := fun x => match x with
      | .sort l => pure (.done (.sort l.normalize))
      | .const n ls => pure (.done (.const n (ls.map Lean.Level.normalize)))
      | _ => pure .continue)
  let erase : Lean.Expr → Lean.Expr := fun f => match f with
    | .const n ls => .const n (ls.map fun _ => .zero)
    | f => f
  -- The head constant of an application keeps its universe levels until the arguments' kinds have been read from
  -- it (`skipConstInApp`), since a level set to zero can turn a type argument's sort into `Prop`.
  let keyOf : Lean.Expr → Lean.MetaM UInt64 := fun e => do
    let e' ← Lean.Meta.transform e (skipConstInApp := true) (post := fun x => do
      match x with
      | .const .. => return .done (erase x)
      | .forallE _ d b _ => return .done (.forallE `x d b .default)
      | .lam _ d b _ => return .done (.lam `x d b .default)
      | .letE _ _ v b nd => return .done (.letE `x (.sort .zero) v b nd)
      | .mdata _ a => return .done a
      | .app .. =>
        let f := x.getAppFn
        let args := x.getAppArgs
        let info ← if f.hasLooseBVars then pure ({} : Lean.Meta.FunInfo)
          else Lean.Meta.getFunInfoNArgs f args.size
        let mut newArgs := args
        for i in [0:args.size] do
          if h : i < info.paramInfo.size then
            let p := info.paramInfo[i]
            if !(p.isExplicit && !p.isProp) then
              newArgs := newArgs.set! i (.sort .zero)
        return .done (Lean.mkAppN (erase f) newArgs)
      | _ => return .continue)
    return e'.hash
  let mut terms : Array (Option Lean.Expr) := #[]
  let mut keys : Array UInt64 := #[]
  let mut elabNanos : Array Nat := #[]
  for entry in entries do
    let start ← IO.monoNanosNow
    let s ← Lean.ofExcept (entry.getObjValAs? String "pp")
    let levels ← Lean.ofExcept (entry.getObjValAs? (Array String) "levels")
    let hyps ← Lean.ofExcept (entry.getObjValAs? Nat "hyps")
    let e? ← try
        Lean.withCurrHeartbeats do
          let stx ← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `term s)
          let e ← Lean.Elab.Term.withLevelNames (levels.toList.map Lean.Name.mkSimple) do
            Lean.Elab.Term.withoutErrToSorry do
              let e ← Lean.Elab.Term.elabTerm stx none
              Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
              Lean.instantiateMVars e
          if e.hasMVar then return none
          let e ← normalize e
          -- The number of hypotheses is part of the key: `h : P ⊢ Q` and `⊢ P → Q` have one closed type but are
          -- different goals.
          return some (e, mixHash (← keyOf e) (hash hyps))
      catch _ => pure none
    terms := terms.push (e?.map Prod.fst)
    keys := keys.push ((e?.map Prod.snd).getD 0)
    elabNanos := elabNanos.push ((← IO.monoNanosNow) - start)
  let mut result : Array (String × Lean.Json) := #[("elabNanos", Lean.toJson elabNanos),
    ("elaborated", Lean.toJson (terms.map Option.isSome))]
  for (label, mode) in [("reducible", Lean.Meta.TransparencyMode.reducible),
                        ("instances", Lean.Meta.TransparencyMode.instances),
                        ("default", Lean.Meta.TransparencyMode.default)] do
    let mut buckets : Std.HashMap UInt64 (Array Nat) := {}
    let mut classes : Array Int := #[]
    let mut nanos : Array Nat := #[]
    let mut checks := 0
    let mut accepted := 0
    let mut exhausted := 0
    for i in [0:terms.size] do
      match terms[i]! with
      | none =>
        classes := classes.push (-1)
        nanos := nanos.push 0
      | some e =>
        let start ← IO.monoNanosNow
        let k := keys[i]!
        let mut found : Option Nat := none
        for j in buckets.getD k #[] do
          checks := checks + 1
          let verdict ← try
              Lean.withCurrHeartbeats <| Lean.Meta.withTransparency mode <|
                Lean.Meta.isDefEq e terms[j]!.get!
            catch _ =>
              exhausted := exhausted + 1
              pure false
          if verdict then
            accepted := accepted + 1
            found := some j
            break
        match found with
        | some j => classes := classes.push (Int.ofNat classes[j]!.toNat)
        | none =>
          buckets := buckets.insert k ((buckets.getD k #[]).push i)
          classes := classes.push (Int.ofNat i)
        nanos := nanos.push ((← IO.monoNanosNow) - start)
    result := result.push (label, Lean.Json.mkObj [("classes", Lean.toJson classes), ("nanos", Lean.toJson nanos),
      ("checks", Lean.toJson checks), ("accepted", Lean.toJson accepted), ("exhausted", Lean.toJson exhausted)])
  Lean.logInfo (Lean.Json.mkObj result.toList).compress"""


def _info(response: dict[str, Any]) -> Any:
    if any(m.get("severity") == "error" for m in response.get("messages", [])):
        return None
    infos = [m["data"] for m in response.get("messages", []) if m.get("severity") == "info"]
    if len(infos) != 1:
        return None
    try:
        return json.loads(infos[0])
    except json.JSONDecodeError:
        return None


def closed_types(repl: LeanRepl, proof_state: int) -> list[dict[str, Any]] | None:
    """Each goal of a proof state as `CLOSED_TACTIC` exports it, or None if the export fails."""
    try:
        response = repl._exchange({"tactic": f"set_option maxHeartbeats {HEARTBEATS} in\n{CLOSED_TACTIC}",
                                   "proofState": proof_state}, repl.timeout)
    except ReplTimeout:
        return None
    out = _info(response)
    return out if isinstance(out, list) else None


def defeq_tactic(path: str) -> str:
    return DEFEQ_TEMPLATE.replace("PATH", json.dumps(path))


def canonical_classes(repl: LeanRepl, proof_state: int, path: str, timeout: float) -> dict[str, Any] | None:
    """The classes of the goals listed in `path` (a JSON array of {"pp", "levels"}), at reducible and instances
    transparency, with elaboration and merge times; None if the tactic fails."""
    try:
        response = repl._exchange({"tactic": f"set_option maxHeartbeats {DEFEQ_HEARTBEATS} in\n{defeq_tactic(path)}",
                                   "proofState": proof_state}, timeout)
    except ReplTimeout:
        return None
    out = _info(response)
    return out if isinstance(out, dict) else None
