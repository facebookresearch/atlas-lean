/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lean
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Tactic.Translate.ToDual

/-!
Dump, for every constant declared in the given modules, what the Mathlib layer of the dependency
graph needs: its module, kind and flags (private, instance, deprecated, auxiliary), docstring,
declaration line, pretty-printed signature, and the constants of the kept libraries its type and
its value use. The uses follow `scripts/dump_v2_dependencies.lean`: an inductive type has no value,
so its constructors' types stand in for one. One JSON object per line;
`scripts/extract_mathlib_graph.py` runs the shards and collapses the rows onto graph nodes.

    lake env lean --run scripts/dump_mathlib_dependencies.lean MODULE_LIST KEEP SHARD SHARDS > OUT.jsonl

* `MODULE_LIST` names one module per line. Every listed module is imported (with its private
  part), and the constants of the listed modules whose line index is `SHARD` modulo `SHARDS` get
  a row.
* `KEEP` is a comma-separated list of module roots: a used constant is recorded when the module
  declaring it starts with one of them (`Mathlib` for the Mathlib graph,
  `Mathlib,MathlibExt,CSLibExt,PhyslibExt,Domains,WantedExt` for ATLAS's bridge edges).
-/

open Lean Meta

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

/-- Namespace roots of tactic and programming infrastructure outside Mathlib (`Lean.Syntax`,
`Lean.Meta.MetaM`, `Qq.Quoted`, ...). The row lists the constants under them that its type uses. -/
def metaRoots : NameSet :=
  [`Lean, `Qq, `Aesop, `ProofWidgets, `Plausible, `ImportGraph, `LeanSearchClient].foldl
    (·.insert ·) {}

/-- Why Lean itself treats the constant as generated machinery rather than a user declaration. -/
def auxReason (env : Environment) (name : Name) (info : ConstantInfo) : Option String :=
  let user := privateToUserName name
  if user.isInternalDetail then some "internal"  -- `_`-prefixed parts, `eq_1`, `match_1`, `proof_1`
  else if info matches .recInfo _ then some "recursor"
  else if isAuxRecursor env name then some "aux_recursor"  -- casesOn, recOn, brecOn, below, ...
  else if isNoConfusion env name || user matches .str _ "noConfusionType" then some "no_confusion"
  else if Meta.isMatcherCore env name then some "matcher"
  else if isSparseCasesOn env name then some "aux_recursor"
  else if isReservedName env name then some "reserved"  -- eq_def, induct, injEq, congr_simp, ...
  else none

def optName : Option Name → Json
  | some n => toJson n.toString
  | none => Json.null

def names (ns : Array Name) : Json :=
  Json.arr (ns.map (toJson ·.toString))

/-- Distinct names, in a fixed order. -/
def dedupSorted (ns : Array Name) : Array Name :=
  (ns.foldl (·.insert ·) ({} : NameSet)).toArray.qsort (·.toString < ·.toString)

def main (args : List String) : IO UInt32 := do
  let [listFile, keepArg, shardArg, shardsArg] := args
    | IO.eprintln "usage: dump_mathlib_dependencies.lean MODULE_LIST KEEP SHARD SHARDS"; return 2
  let (some shard, some shards) := (shardArg.toNat?, shardsArg.toNat?)
    | IO.eprintln "SHARD and SHARDS must be natural numbers"; return 2
  let modules := ((← IO.FS.lines listFile).filter (· ≠ "")).map String.toName
  let keepRoots : NameSet := ((keepArg.splitOn ",").filter (· ≠ "")).foldl (·.insert ·.toName) {}
  let mine : NameSet := (modules.zipIdx.filter fun (_, i) => i % shards == shard).foldl
    (fun s (m, _) => s.insert m) {}
  initSearchPath (← findSysroot)
  -- Environment extensions (instances, classes, simp lemmas, `to_additive`) need their imported
  -- state, which runs their import functions, possibly in the interpreter.
  unsafe enableInitializersExecution
  let env ← importModules (modules.map fun module => { module, importAll := true }) {}
    (trustLevel := 1024) (loadExts := true)
  -- `moduleNames` builds a new array on each call: take it once (see `dump_v2_dependencies.lean`).
  let moduleNames := env.header.moduleNames
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map (moduleNames[·]!)
  let kept (n : Name) : Bool := (moduleOf n).any (keepRoots.contains ·.getRoot)
  let uses (es : Array Expr) : Array Name :=
    dedupSorted ((es.flatMap (·.getUsedConstants)).filter kept)
  let metaUses (e : Expr) : Array Name :=
    dedupSorted (e.getUsedConstants.filter fun c => !kept c && metaRoots.contains c.getRoot)
  let rows := env.constants.fold (init := #[]) fun acc name info =>
    if (moduleOf name).any mine.contains then acc.push (name, info) else acc
  -- Parent projections and the structure each belongs to, including the generated `toB` of a
  -- parent that is not a subobject. A structure and its parents' projections share a module.
  let parentProjections : NameMap Name := rows.foldl (init := {}) fun m (name, _) =>
    if isStructure env name then
      (getStructureParentInfo env name).foldl (fun m parent => m.insert parent.projFn name) m
    else m
  let stdout ← IO.getStdout
  let opts : Options := ({} : Options).setBool `pp.unicode.fun true
  let ctx : Core.Context :=
    { fileName := "<dump_mathlib_dependencies>", fileMap := default, options := opts }
  let work : CoreM Unit := do
    let simpLemmas ← getSimpTheorems
    for (name, info) in rows do
      let some module := moduleOf name | continue
      let value := match info with
        | .inductInfo val =>
          uses (val.ctors.filterMap fun ctor => (env.find? ctor).map (·.type)).toArray
        | _ => uses ((info.value? (allowOpaque := true)).map (#[·]) |>.getD #[])
      let aux := auxReason env name info
      let private_ := isPrivateName name
      let deprecation := Linter.deprecatedAttr.getParam? env name
      let kind := kindOf info
      let candidate := !private_ && aux.isNone && deprecation.isNone &&
        !(kind == "recursor" || kind == "constructor" || kind == "quot")
      let projection : Json := match env.getProjectionFnInfo? name with
        | some p =>
          let struct := p.ctorName.getPrefix
          let field := Name.mkSimple (name.componentsRev.headD .anonymous).toString
          Json.mkObj [("structure", toJson struct.toString), ("field", toJson field.toString),
            ("subobject", toJson (isSubobjectField? env struct field).isSome),
            ("from_class", toJson p.fromClass)]
        | none => Json.null
      let doc ← findDocString? env name
      let ranges ← findDeclarationRanges? name
      let reducibility ← getReducibilityStatus name
      -- What needs elaboration (whether the type is a proposition, the signature) runs with a
      -- fresh heartbeat budget; a failure leaves the field null instead of stopping the dump.
      let prop : Option Bool ← if candidate || projection != Json.null then
          Core.tryCatchRuntimeEx (withCurrHeartbeats (some <$> (isProp info.type).run'))
            fun _ => pure none
        else pure none
      let signature : Option String ← if candidate then
          Core.tryCatchRuntimeEx (withCurrHeartbeats (some <$> (do
              return (← PrettyPrinter.ppSignature name).fmt.pretty 120).run'))
            fun _ => pure none
        else pure none
      let head := info.type.getForallBody.getAppFn.constName?
      let row := Json.mkObj [
        ("name", toJson name.toString),
        ("module", toJson module.toString),
        ("kind", toJson kind),
        ("private", toJson private_),
        ("aux", match aux with | some r => toJson r | none => Json.null),
        ("instance", toJson (isInstanceCore env name)),
        ("class", toJson (isClass env name)),
        ("structure", toJson (isStructure env name)),
        ("projection", projection),
        ("parent_projection", optName (parentProjections.find? name)),
        ("deprecated", match deprecation with
          | some d => Json.mkObj [("new", optName d.newName?),
              ("since", match d.since? with | some s => toJson s | none => Json.null)]
          | none => Json.null),
        ("reducibility", toJson (match reducibility with
          | .reducible => "reducible" | .semireducible => "semireducible"
          | .irreducible => "irreducible" | .implicitReducible => "implicit_reducible"
          | .instanceReducible => "instance_reducible")),
        ("unsafe", toJson info.isUnsafe),
        ("meta", toJson (isMarkedMeta env name)),
        ("prop", match prop with | some b => toJson b | none => Json.null),
        ("head", optName head),
        ("ctors", match info with
          | .inductInfo val => names val.ctors.toArray
          | _ => Json.null),
        ("mutual", if info.all.length > 1 then names info.all.toArray else Json.null),
        ("doc", match doc with | some d => toJson d | none => Json.null),
        ("line", match ranges with | some r => toJson r.range.pos.line | none => Json.null),
        ("name_line", match ranges with
          | some r => toJson r.selectionRange.pos.line | none => Json.null),
        ("to_additive", optName ((Mathlib.Tactic.ToAdditive.translations.find? env name).map
          (·.translation))),
        ("to_dual", optName ((Mathlib.Tactic.ToDual.translations.find? env name).map
          (·.translation))),
        ("simp", toJson (simpLemmas.isLemma (.decl name))),
        ("type_meta", names (metaUses info.type)),
        ("signature", match signature with | some s => toJson s | none => Json.null),
        ("type", names (uses #[info.type])),
        ("value", names value)]
      stdout.putStrLn row.compress
  let _ ← work.toIO ctx { env }
  return 0
