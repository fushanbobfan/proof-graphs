#!/usr/bin/env python3
"""Syntactic goal identity on instantiated Lean expression trees.

Names and literals are opaque. Context positions and de Bruijn indices erase local and binder names;
out-of-context free variables retain their identities. Term and level metavariables have separate joint
numberings. These keys do not quotient definitional equality. An unavailable export must never be merged.

KEY_TACTIC can be used directly, or defined once as a tactic by replacing its initial `run_tac do`, as in
search_faithful.ExportingSession. export also accepts the name of such a defined tactic.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from typing import Any

from lean_repl import LeanRepl, ReplTimeout

HEARTBEATS = 400000
KEY_TACTIC = r"""run_tac do
  let rec nameJson : Lean.Name → Lean.Json
    | .anonymous => Lean.Json.arr #[]
    | .str p s => Lean.Json.arr #[nameJson p, Lean.Json.str s]
    | .num p n => Lean.Json.arr #[nameJson p, Lean.toJson n]
  let nameId := fun n => (nameJson n).compress
  let node := fun k fields => Lean.Json.mkObj (("kind", Lean.Json.str k) :: fields)
  let bic : Lean.BinderInfo → String := fun
    | .default => "explicit" | .implicit => "implicit"
    | .strictImplicit => "strict_implicit" | .instImplicit => "instance"
  let rec level : Lean.Level → Lean.Json
    | .zero => node "zero" []
    | .succ l => node "succ" [("of", level l)]
    | .max a b => node "max" [("left", level a), ("right", level b)]
    | .imax a b => node "imax" [("left", level a), ("right", level b)]
    | .param n => node "param" [("name", Lean.Json.str (nameId n))]
    | .mvar m => node "lmvar" [("id", Lean.Json.str (nameId m.name))]
  let mut goals : Array Lean.Json := #[]
  for g in (← Lean.Elab.Tactic.getGoals) do
    let decl ← g.getDecl
    let mut pos : Std.HashMap Lean.FVarId Nat := {}
    let mut ldecls : Array Lean.LocalDecl := #[]
    for d? in decl.lctx.decls.toArray do
      if let some d := d? then
        pos := pos.insert d.fvarId ldecls.size
        ldecls := ldecls.push d
    let posF := pos
    let rec ser : Lean.Expr → Lean.Json
      | .bvar i => node "bvar" [("index", Lean.toJson i)]
      | .fvar f => match posF.get? f with
        | some p => node "fvar" [("position", Lean.toJson p)]
        | none => node "external_fvar" [("id", Lean.Json.str (nameId f.name))]
      | .mvar m => node "mvar" [("id", Lean.Json.str (nameId m.name))]
      | .sort l => node "sort" [("level", level l)]
      | .const n ls => node "const" [("name", Lean.Json.str (nameId n)),
          ("levels", Lean.toJson (ls.map level))]
      | .app f a => node "app" [("function", ser f), ("argument", ser a)]
      | .lam _ t b bi => node "lambda" [("binder_info", Lean.Json.str (bic bi)),
          ("type", ser t), ("body", ser b)]
      | .forallE _ t b bi => node "pi" [("binder_info", Lean.Json.str (bic bi)),
          ("type", ser t), ("body", ser b)]
      | .letE _ t v b _ => node "let" [("type", ser t), ("value", ser v), ("body", ser b)]
      | .lit (.natVal n) => node "nat" [("value", Lean.Json.str (toString n))]
      | .lit (.strVal s) => node "string" [("value", Lean.Json.str s)]
      | .mdata _ e => ser e
      | .proj n i e => node "projection" [("name", Lean.Json.str (nameId n)),
          ("index", Lean.toJson i), ("expression", ser e)]
    let hyps ← g.withContext do
      ldecls.mapM fun d => do
        let t ← Lean.instantiateMVars d.type
        let v ← match d.value? with
          | some e => do pure (ser (← Lean.instantiateMVars e))
          | none => pure Lean.Json.null
        pure (Lean.Json.mkObj [("type", ser t), ("value", v),
          ("binder_info", Lean.Json.str (bic d.binderInfo)),
          ("implementation_detail", Lean.toJson d.isImplementationDetail)])
    let target ← g.withContext do pure (ser (← Lean.instantiateMVars decl.type))
    goals := goals.push (Lean.Json.mkObj [("id", Lean.Json.str (nameId g.name)),
      ("hyps", Lean.toJson hyps), ("target", target)])
  Lean.logInfo (Lean.Json.arr goals).compress"""

BINDERS = {"explicit", "implicit", "strict_implicit", "instance"}
EXPR_FIELDS = {
    "bvar": ("index",), "fvar": ("position",), "external_fvar": ("id",), "mvar": ("id",),
    "sort": ("level",), "const": ("name", "levels"), "app": ("function", "argument"),
    "lambda": ("binder_info", "type", "body"), "pi": ("binder_info", "type", "body"),
    "let": ("type", "value", "body"), "nat": ("value",), "string": ("value",),
    "projection": ("name", "index", "expression"),
}
LEVEL_FIELDS = {"zero": (), "succ": ("of",), "max": ("left", "right"),
                "imax": ("left", "right"), "param": ("name",), "lmvar": ("id",)}


def _fields(value: Any, names: tuple[str, ...]) -> None:
    if not isinstance(value, dict) or set(value) != set(names):
        raise ValueError(f"expected fields {names}")


def _renumber(goals: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Visit goal ids first, then each context (type before value), then target, in list order."""
    terms: dict[str, int] = {}
    levels: dict[str, int] = {}
    for goal in goals:
        _fields(goal, ("id", "hyps", "target"))
        if not isinstance(goal["id"], str) or not isinstance(goal["hyps"], list):
            raise ValueError("invalid goal id or context")
        terms.setdefault(goal["id"], len(terms))

    def tree(value: Any, level: bool = False, context_size: int = 0) -> dict[str, Any]:
        fields = LEVEL_FIELDS if level else EXPR_FIELDS
        if not isinstance(value, dict) or value.get("kind") not in fields:
            raise ValueError("unknown tree node")
        kind = value["kind"]
        _fields(value, ("kind",) + fields[kind])
        out: dict[str, Any] = {"kind": kind}
        for field in fields[kind]:
            item = value[field]
            if field == "id" and kind in ("mvar", "lmvar"):
                if not isinstance(item, str):
                    raise ValueError("invalid metavariable id")
                numbering = levels if level else terms
                out[field] = numbering.setdefault(item, len(numbering))
            elif field in ("name", "id", "value") and kind != "let":
                if not isinstance(item, str) or (kind == "nat" and
                                                (not item.isascii() or not item.isdecimal())):
                    raise ValueError("invalid name, id or literal")
                out[field] = item
            elif field in ("index", "position"):
                if type(item) is not int or item < 0 or (field == "position" and item >= context_size):
                    raise ValueError("invalid variable position or projection index")
                out[field] = item
            elif field == "binder_info":
                if item not in BINDERS:
                    raise ValueError("invalid binder info")
                out[field] = item
            elif field == "levels":
                if not isinstance(item, list):
                    raise ValueError("invalid constant levels")
                out[field] = [tree(l, True, context_size) for l in item]
            else:
                out[field] = tree(item, level or field == "level", context_size)
        return out

    out = []
    for goal in goals:
        hyps = []
        for hyp in goal["hyps"]:
            _fields(hyp, ("type", "value", "binder_info", "implementation_detail"))
            if hyp["binder_info"] not in BINDERS or type(hyp["implementation_detail"]) is not bool:
                raise ValueError("invalid local declaration")
            hyps.append({"type": tree(hyp["type"], context_size=len(goal["hyps"])),
                         "value": None if hyp["value"] is None else
                         tree(hyp["value"], context_size=len(goal["hyps"])),
                         "binder_info": hyp["binder_info"],
                         "implementation_detail": hyp["implementation_detail"]})
        out.append({"id": terms[goal["id"]], "hyps": hyps,
                    "target": tree(goal["target"], context_size=len(goal["hyps"]))})
    return out


def export(repl: LeanRepl, proof_state: int, tactic: str | None = None) -> list[dict[str, Any]] | None:
    """Return the complete typed goal list, or None on timeout, error, or any malformed export."""
    text = f"set_option maxHeartbeats {HEARTBEATS} in\n{tactic or KEY_TACTIC}"
    try:
        response = repl._exchange({"tactic": text, "proofState": proof_state}, repl.timeout)
    except ReplTimeout:
        return None
    if any(m.get("severity") == "error" for m in response.get("messages", [])):
        return None
    infos = [m["data"] for m in response.get("messages", []) if m.get("severity") == "info"]
    if len(infos) != 1:
        return None
    try:
        goals = json.loads(infos[0])
        if not isinstance(goals, list):
            return None
        _renumber(goals)
    except (ValueError, TypeError, KeyError, RecursionError):
        return None
    return goals


def _serialization(goals: list[dict[str, Any]]) -> str:
    return json.dumps(_renumber(goals), ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def ordered_state_key(goals: list[dict[str, Any]]) -> str:
    """A goal list in order, with one joint renaming."""
    return _digest(_serialization(goals))


def unordered_state_key(goals: list[dict[str, Any]], max_goals: int = 7) -> str | None:
    """Minimum jointly renamed serialization over permutations; None above the factorial-work bound.

    Callers must treat None as unequal to everything, including another None: it is not a merge key.
    """
    if len(goals) > max_goals:
        return None
    return _digest(min(_serialization(list(order)) for order in itertools.permutations(goals)))


def goal_key(goal: dict[str, Any]) -> str:
    """One goal alone, blind to sharing with other goals; never use it to compare states."""
    return ordered_state_key([goal])


def group_key(goals: list[dict[str, Any]]) -> str:
    """A coupled group jointly renamed in its state order."""
    return ordered_state_key(goals)


def groups(goals: list[dict[str, Any]]) -> list[list[int]]:
    """Partition goal indices by transitive term- and level-metavariable coupling.

    Detects occurrences after instantiation: a goal mentioning another goal's own term metavariable,
    shared third unassigned term metavariables, and shared level metavariables, in contexts or targets.
    Does not detect dependencies through delayed assignments whose metavariables do not occur, or
    through tactics' side state. Term and level names inhabit separate namespaces.
    """
    _renumber(goals)
    parent = list(range(len(goals)))

    def find(i: int) -> int:
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    def occurrences(value: Any) -> set[tuple[str, str]]:
        if isinstance(value, dict):
            if value.get("kind") in ("mvar", "lmvar"):
                return {(value["kind"], value["id"])}
            return set().union(*(occurrences(v) for v in value.values()))
        if isinstance(value, list):
            return set().union(*(occurrences(v) for v in value))
        return set()

    seen: dict[tuple[str, str], int] = {}
    for i, goal in enumerate(goals):
        occurrence = ("mvar", goal["id"])
        if occurrence in seen:
            parent[find(i)] = find(seen[occurrence])
        else:
            seen[occurrence] = i
    for i, goal in enumerate(goals):
        for occurrence in occurrences([goal["hyps"], goal["target"]]):
            if occurrence in seen:
                parent[find(i)] = find(seen[occurrence])
            else:
                seen[occurrence] = i
    out: dict[int, list[int]] = {}
    for i in range(len(goals)):
        out.setdefault(find(i), []).append(i)
    return sorted(out.values(), key=lambda members: members[0])
