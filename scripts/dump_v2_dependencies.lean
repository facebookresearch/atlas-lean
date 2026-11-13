/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lean

/-!
Dump, for every constant declared in the given ATLAS v2 modules, the v2 constants
its type and its value (including theorem proofs) use, and whether it is private,
documented or an instance. An inductive type has no value, so its constructors'
types stand in for one: they hold a structure's fields and a class's parents. One JSON object per line;
`scripts/extract_v2_lean_dependencies.py` collapses the result onto wiki articles.

    lake env lean --run scripts/dump_v2_dependencies.lean MODULE_LIST > OUT.jsonl

`MODULE_LIST` names one module per line.
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

def main (args : List String) : IO UInt32 := do
  let some listFile := args.head?
    | IO.eprintln "usage: lean --run dump_v2_dependencies.lean MODULE_LIST"; return 2
  let names := ((← IO.FS.lines listFile).filter (· ≠ "")).map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules (names.map fun module => { module, importAll := true }) {}
    (trustLevel := 1024)
  let mine : NameSet := names.foldl (·.insert ·) {}
  -- `moduleNames` builds a new array of every imported module's name on each
  -- call. Called once per constant a declaration uses, it kept the dump busy
  -- for 51 minutes instead of one.
  let moduleNames := env.header.moduleNames
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map (moduleNames[·]!)
  let inMine (n : Name) : Bool := (moduleOf n).any mine.contains
  let uses (es : Array Expr) : Json :=
    Json.arr (((es.flatMap (·.getUsedConstants)).filter inMine).map (toJson ·.toString))
  let stdout ← IO.getStdout
  for (name, info) in env.constants.toList do
    let some module := moduleOf name | continue
    unless mine.contains module do continue
    let value := match info with
      | .inductInfo val => uses (val.ctors.filterMap fun ctor => (env.find? ctor).map (·.type)).toArray
      | _ => uses ((info.value? (allowOpaque := true)).map (#[·]) |>.getD #[])
    let doc := (← findDocString? env name).isSome
    stdout.putStrLn (Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson module.toString),
      ("kind", toJson (kindOf info)),
      ("private", toJson (isPrivateName name)),
      ("doc", toJson doc),
      ("instance", toJson (Meta.isInstanceCore env name)),
      ("type", uses #[info.type]),
      ("value", value)]).compress
  return 0
