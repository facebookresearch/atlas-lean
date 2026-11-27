/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Snapshot a compiled module using Lean's import and axiom APIs.
Run one module per process with the saved import artifact paths.
-/
import Lean
import Lean.CoreM
import Lean.Setup
import Lean.Util.CollectAxioms

open Lean

private partial def firstUnpinnedImport (module : Name) (visibility : OLeanLevel)
    (arts : NameMap ImportArtifacts) (seen : IO.Ref (Std.HashMap Name OLeanLevel))
    : IO (Option Name) := do
  if let some previous := (← seen.get)[module]? then
    if previous ≥ visibility then return none
  seen.modify fun levels => levels.insert module visibility
  let some artifacts := arts.find? module | return some module
  let parts ← readModuleDataParts (artifacts.oleanParts (inServer := true))
  let some first := parts[0]? | throw <| IO.userError s!"No module data for {module}"
  let data ← if first.1.isModule && visibility == .private then do
    let some priv := parts[2]? | throw <| IO.userError s!"No private module data for {module}"
    pure priv.1
    else pure first.1
  for dependency in data.imports do
    let childVisibility := if data.isModule && visibility == .private && dependency.importAll then
      .private else .exported
    if let some missing ← firstUnpinnedImport dependency.module childVisibility arts seen then
      return some missing
  return none

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def declarationsJson (moduleIdx : ModuleIdx) (exportedNames : NameSet) :
    CoreM (Array Json) := do
  let env ← getEnv
  let names := env.header.moduleData[moduleIdx]!.constNames.qsort Name.quickLt
  let mut rows := #[]
  for name in names do
    let some info := env.find? name | throwError "Missing module declaration: {name}"
    unless env.getModuleIdxFor? name == some moduleIdx do
      throwError "Declaration has a different owning module: {name}"
    let axioms := (← collectAxioms name).qsort Name.quickLt
    let value := if info.isTheorem then none else info.value? (allowOpaque := true)
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("level_params", toJson (info.levelParams.map Name.toString)),
      ("kind", toJson (declarationKind info)),
      ("type", toJson (reprStr info.type)),
      ("value", toJson (value.map reprStr)),
      ("is_unsafe", toJson info.isUnsafe),
      ("is_partial", toJson info.isPartial),
      ("is_exported", toJson (exportedNames.contains name)),
      ("is_private_name", toJson (isPrivateName name)),
      ("axioms", toJson (axioms.map Name.toString))]
  return rows

private unsafe def probe (module : Name) (setup : ModuleSetup) : IO Json := do
  initSearchPath (← findSysroot)
  let some arts := setup.importArts.find? module |
    throw <| IO.userError s!"Requested module has no pinned import artifacts: {module}"
  let some olean := arts.olean? |
    throw <| IO.userError s!"Requested module has no pinned olean: {module}"
  let (exportedData, _) ← readModuleData olean
  let exportedNames := exportedData.constNames.foldl (fun names name => names.insert name)
    ({} : NameSet)
  enableInitializersExecution
  setup.dynlibs.forM Lean.loadDynlib
  let env ← importModules #[{ module, importAll := true }] {}
    (plugins := setup.plugins) (loadExts := true) (level := .private) (arts := setup.importArts)
  let some moduleIdx := env.getModuleIdx? module |
    throw <| IO.userError s!"Requested module was not loaded: {module}"
  unless env.header.modules[moduleIdx]!.importAll do
    throw <| IO.userError s!"Requested module was not imported with private data: {module}"
  let declarations ← (declarationsJson moduleIdx exportedNames).toIO'
    { fileName := "<declaration_probe>", fileMap := default } { env }
  let loaded := env.header.moduleNames.qsort Name.quickLt
  return Json.mkObj [
    ("module", toJson module.toString),
    ("resolved_olean", toJson olean.toString),
    ("uses_module_system", toJson exportedData.isModule),
    ("declaration_count", toJson declarations.size),
    ("declarations", Json.arr declarations),
    ("loaded_module_count", toJson loaded.size),
    ("loaded_modules", toJson (loaded.map Name.toString))]

unsafe def main (args : List String) : IO UInt32 := do
  let [setupFile, moduleName] := args |
    (← IO.getStderr).putStrLn "usage: declaration_probe SETUP MODULE"
    return 2
  let module := moduleName.toName
  if module.isAnonymous then
    (← IO.getStderr).putStrLn "Module name must be nonempty"
    return 2
  try
    let setup ← ModuleSetup.load setupFile
    if let some missing ← firstUnpinnedImport module .private setup.importArts (← IO.mkRef {}) then
      (← IO.getStderr).putStrLn (Json.mkObj [
        ("kind", toJson "missing_private_import_artifacts"),
        ("module", toJson missing.toString)]).compress
      return 3
    IO.println (← probe module setup).compress
    return 0
  catch error =>
    (← IO.getStderr).putStrLn error.toString
    return 1
