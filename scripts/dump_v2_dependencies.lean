/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lean

/-!
Dump, for every constant declared in the given ATLAS v2 modules, the v2 constants
its type and its value (including theorem proofs) use, and whether it is private
or documented. An inductive type has no value, so its constructors'
types stand in for one: they hold a structure's fields and a class's parents. One JSON object per line;
`scripts/extract_v2_lean_dependencies.py` collapses the result onto wiki articles.

    lake env lean --run scripts/dump_v2_dependencies.lean MODULE_LIST [MATHLIB_NAMES] > OUT.jsonl

`MODULE_LIST` names one module per line. `MATHLIB_NAMES`, which
`sync_wiki.py mathlib-names` writes, names the Mathlib declarations wiki pages
credit, one per line, each followed by a tab and its module when the page names
one; those modules are imported too. A named declaration that is a constant of a
Mathlib module, and not of a v2 module, is found; the others are missing. With
the list, every v2 row also lists the found declarations it reaches: through what
its type states (`mathlib_type`), through everything its type uses
(`mathlib_type_used`, for a proof that passes through it), through its value
(`mathlib_value`) and, for a definition or an inductive type, through its value
as part of what it states (`mathlib_state`); it also lists the found
declarations its type and its value name themselves, with no constant between
(`mathlib_type_direct`, `mathlib_value_direct`), the only ones the extraction
keeps as bridges. Each named declaration gets a row of its own,
marked `registered`: a found one with its kind, its module and the same lists
but the last two, a missing one marked `missing`, with whether the list gave its
module (and `project` when it is a v2 constant). The output then opens with a
header naming its format and Mathlib's revision in lake-manifest.json, and
closes with its row counts. Without the list, the output is as before.

A row reaches a found declaration through the constants it uses that are
neither found nor the project's, by the rule the extraction applies to the
project's own constants: its type reaches what those constants state (their
types, a definition's body, an inductive type's constructors' types), and its
value reaches everything they use. Uses through the project's constants are
left to the extraction, which follows them from their own rows.
-/

open Lean

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

/-- The expressions a constant's value consists of: an inductive type's constructors' types. -/
def valueExprs (env : Environment) (info : ConstantInfo) : Array Expr :=
  match info with
  | .inductInfo val => (val.ctors.filterMap fun ctor => (env.find? ctor).map (·.type)).toArray
  | _ => (info.value? (allowOpaque := true)).map (#[·]) |>.getD #[]

/-- What a constant states: its type, a definition's body, and an inductive type's constructors' types. -/
def stateExprs (env : Environment) (info : ConstantInfo) : Array Expr :=
  match info with
  | .defnInfo val => #[info.type, val.value]
  | .inductInfo _ => #[info.type] ++ valueExprs env info
  | _ => #[info.type]

/-- Whether a constant's value is part of what it states: a definition's body, an inductive type's
constructors. A theorem's proof and an opaque body are not. -/
def statesValue : ConstantInfo → Bool
  | .defnInfo _ | .inductInfo _ => true
  | _ => false

/-- Everything a constant uses: its type and its value. -/
def allExprs (env : Environment) (info : ConstantInfo) : Array Expr :=
  #[info.type] ++ valueExprs env info

/-- The distinct constants some expressions use. -/
def usedIn (es : Array Expr) : Array Name :=
  ((es.flatMap (·.getUsedConstants)).foldl (fun (set : NameSet) n => set.insert n) {}).toList.toArray

/-- The union of two small arrays of names, without repeats. -/
def unite (a b : Array Name) : Array Name :=
  b.foldl (fun acc n => if acc.contains n then acc else acc.push n) a

/-- For every constant `follow` accepts that `roots` reach through such constants, the targets it reaches along
`depsOf`, memoized in `sets`. A depth-first pass fills every set; a constant that met one still being computed,
on a cycle, is marked inexact, and the inexact ones are recomputed until nothing grows. -/
partial def reachAll (depsOf : Name → Array Name) (isTarget follow : Name → Bool) (roots : Array Name)
    (sets : Std.HashMap Name (Array Name)) : Std.HashMap Name (Array Name) := Id.run do
  let mut sets := sets
  let mut inexact : Std.HashSet Name := {}
  let contribution (sets : Std.HashMap Name (Array Name)) (d : Name) : Array Name :=
    if isTarget d then #[d] else if follow d then sets.getD d #[] else #[]
  for root in roots do
    unless follow root && !sets.contains root do continue
    let mut onStack : Std.HashSet Name := ({} : Std.HashSet Name).insert root
    let mut stack : Array (Name × Array Name × Nat) := #[(root, depsOf root, 0)]
    while !stack.isEmpty do
      let (n, ds, i) := stack.back!
      if i < ds.size then
        stack := stack.set! (stack.size - 1) (n, ds, i + 1)
        let d := ds[i]!
        if follow d && !isTarget d && !sets.contains d && !onStack.contains d then
          stack := stack.push (d, depsOf d, 0)
          onStack := onStack.insert d
      else
        let mut acc : Array Name := #[]
        let mut cyclic := false
        for d in ds do
          acc := unite acc (contribution sets d)
          if follow d && !isTarget d && (onStack.contains d || inexact.contains d) then cyclic := true
        sets := sets.insert n acc
        if cyclic then inexact := inexact.insert n
        onStack := onStack.erase n
        stack := stack.pop
  let mut changed := true
  while changed do
    changed := false
    for n in inexact.toArray do
      let acc := (depsOf n).foldl (fun acc d => unite acc (contribution sets d)) (sets.getD n #[])
      if acc.size != (sets.getD n #[]).size then
        sets := sets.insert n acc
        changed := true
  return sets

def main (args : List String) : IO UInt32 := do
  let some listFile := args.head?
    | IO.eprintln "usage: lean --run dump_v2_dependencies.lean MODULE_LIST [MATHLIB_NAMES]"; return 2
  let names := ((← IO.FS.lines listFile).filter (· ≠ "")).map String.toName
  let registry : Array (Name × Option Name) ← match (args[1]? : Option String) with
    | none => pure #[]
    | some file => do
      let lines := (← IO.FS.lines (System.FilePath.mk file)).filter (· ≠ "")
      pure <| lines.map fun line =>
        match line.splitOn "\t" with
        | [name, module] => (name.toName, some module.toName)
        | _ => (line.toName, none)
  let registryGiven := args.length > 1
  let extra := registry.filterMap (·.2)
  initSearchPath (← findSysroot)
  let env ← importModules ((names ++ extra).map fun module => { module, importAll := true }) {}
    (trustLevel := 1024)
  let mine : NameSet := names.foldl (·.insert ·) {}
  -- `moduleNames` builds a new array of every imported module's name on each
  -- call. Called once per constant a declaration uses, it kept the dump busy
  -- for 51 minutes instead of one.
  let moduleNames := env.header.moduleNames
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map (moduleNames[·]!)
  let inMine (n : Name) : Bool := (moduleOf n).any mine.contains
  let usesBy (keep : Name → Bool) (es : Array Expr) : Json :=
    Json.arr (((es.flatMap (·.getUsedConstants)).filter keep).map (toJson ·.toString))
  let uses := usesBy inMine
  -- A named declaration is found when it is a constant of a Mathlib module that is not a v2 module.
  let isFound (n : Name) : Bool := match moduleOf n with
    | some module => module.getRoot == `Mathlib && !mine.contains module && env.contains n
    | none => false
  let found : NameSet := registry.foldl (fun set entry => if isFound entry.1 then set.insert entry.1 else set) {}
  let follow (n : Name) : Bool := env.contains n && !inMine n && !found.contains n
  let depsWith (exprsOf : Environment → ConstantInfo → Array Expr) (n : Name) : Array Name :=
    match env.find? n with
    | some info => usedIn (exprsOf env info)
    | none => #[]
  let mut stated : Std.HashMap Name (Array Name) := {}
  let mut used : Std.HashMap Name (Array Name) := {}
  if registryGiven && !found.isEmpty then
    -- Every constant outside the project that a v2 constant or a found declaration uses roots a walk: what
    -- its type, and a definition's body or an inductive type's constructors, use roots a walk through what
    -- constants state; what its value uses roots one through everything they use.
    let mut typeRoots : Array Name := #[]
    let mut valueRoots : Array Name := #[]
    for (name, info) in env.constants.toList do
      if inMine name || found.contains name then
        let value := (usedIn (valueExprs env info)).filter follow
        let type := (usedIn #[info.type]).filter follow
        typeRoots := typeRoots ++ type ++ (if statesValue info then value else #[])
        valueRoots := valueRoots ++ type ++ value
    stated := reachAll (depsWith stateExprs) found.contains follow typeRoots {}
    used := reachAll (depsWith allExprs) found.contains follow valueRoots {}
  -- The found declarations some expressions reach, other than `self`: an inductive type's constructors name it.
  let reached (sets : Std.HashMap Name (Array Name)) (es : Array Expr) (self : Name := .anonymous) : Json :=
    if found.isEmpty then Json.arr #[] else
    Json.arr ((((usedIn es).foldl (fun acc d =>
      unite acc (if found.contains d then #[d] else if follow d then sets.getD d #[] else #[])) #[]).filter
      (· != self)).qsort (·.toString < ·.toString) |>.map (toJson ·.toString))
  -- The found declarations some expressions name themselves, with no constant between.
  let named (es : Array Expr) : Json :=
    Json.arr (((usedIn es).filter found.contains).qsort (·.toString < ·.toString) |>.map (toJson ·.toString))
  let stdout ← IO.getStdout
  -- With the list, the output opens with what made it and closes with its row counts, so the extraction can
  -- tell it from an older format or a cut file; without the list it is as before.
  let mathlibRev : Json ← do
    let manifest : System.FilePath := "lake-manifest.json"
    if ← manifest.pathExists then
      match Json.parse (← IO.FS.readFile manifest) with
      | .ok json =>
        let packages := (json.getObjValD "packages").getArr?.toOption.getD #[]
        pure <| (packages.find? (fun p => p.getObjValD "name" == toJson "mathlib")).map
          (·.getObjValD "rev") |>.getD Json.null
      | .error _ => pure Json.null
    else pure Json.null
  if registryGiven then
    stdout.putStrLn (Json.mkObj [("dump", toJson "atlas-v2-dependencies"), ("format", toJson 5),
      ("closure", toJson "statement-and-all-uses"), ("mathlib_rev", mathlibRev),
      ("names", toJson registry.size)]).compress
  let mut projectRows : Nat := 0
  for (name, info) in env.constants.toList do
    let some module := moduleOf name | continue
    unless mine.contains module do continue
    let value := valueExprs env info
    let doc := (← findDocString? env name).isSome
    let fields := [
      ("name", toJson name.toString),
      ("module", toJson module.toString),
      ("kind", toJson (kindOf info)),
      ("private", toJson (isPrivateName name)),
      ("doc", toJson doc),
      ("type", uses #[info.type]),
      ("value", uses value)]
    let credits := if registryGiven then
      [("mathlib_type", reached stated #[info.type]), ("mathlib_type_used", reached used #[info.type]),
        ("mathlib_value", reached used value), ("mathlib_type_direct", named #[info.type]),
        ("mathlib_value_direct", named value)] ++
        (if statesValue info then [("mathlib_state", reached stated value)] else []) else []
    stdout.putStrLn (Json.mkObj (fields ++ credits)).compress
    projectRows := projectRows + 1
  -- Whether a declaration's type is a proposition: what decides if it states a result or defines a concept.
  let isProposition (type : Expr) : IO Bool := do
    let (answer, _) ← (Meta.MetaM.run' (Meta.isProp type)).toIO { fileName := "<dump>", fileMap := default }
      { env := env }
    pure answer
  for (name, givenModule) in registry do
    match env.find? name, found.contains name with
    | some info, true =>
      let value := valueExprs env info
      let proposition ← isProposition info.type
      stdout.putStrLn (Json.mkObj ([
        ("name", toJson name.toString),
        ("module", toJson ((moduleOf name).getD .anonymous).toString),
        ("kind", toJson (kindOf info)),
        ("structure", toJson (isStructure env name)),
        ("proposition", toJson proposition),
        ("class", toJson (isClass env name)),
        ("registered", toJson true),
        ("type", Json.arr #[]),
        ("value", Json.arr #[]),
        ("mathlib_type", reached stated #[info.type] name),
        ("mathlib_type_used", reached used #[info.type] name),
        ("mathlib_value", reached used value name)] ++
        (if statesValue info then [("mathlib_state", reached stated value name)] else []))).compress
    | _, _ =>
      -- A name of the project's own is missing from Mathlib; its row says so, beside the project's own row.
      stdout.putStrLn (Json.mkObj ([
        ("name", toJson name.toString),
        ("registered", toJson true),
        ("missing", toJson true), ("module_given", toJson givenModule.isSome)] ++
        (if inMine name then [("project", toJson true)] else []))).compress
  if registryGiven then
    stdout.putStrLn (Json.mkObj [("end", toJson true), ("rows", toJson projectRows),
      ("names", toJson registry.size)]).compress
  return 0
