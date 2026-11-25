/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Suggest imports from compiled declarations using the pinned ImportGraph API.
Syntax, tactics, and downstream public coverage still require real builds.
-/
module

import all Lean.Environment
public meta import Lean
public meta import ImportGraph.Tools.MinImports

meta section

open Lean

private def currentModuleEnv (env : Environment) (idx : ModuleIdx) (moduleName : Name) :
    Environment := Id.run do
  let data := env.header.moduleData[idx]!
  let mut constants := env.toKernelEnv.constants.switch
  for info in data.constants do
    constants := constants.insert info.name info
  return .ofKernelEnv { env.toKernelEnv with
    constants
    header := { env.header with mainModule := moduleName, imports := data.imports } }

private def probe (moduleName : Name) : IO Json := do
  initSearchPath (← findSysroot)
  let olean ← findOLean moduleName
  let env ← importModules #[{ module := moduleName, importAll := true }] {}
    (loadExts := false) (level := .private)
  let some idx := env.getModuleIdx? moduleName |
    throw <| IO.userError s!"Requested module was not loaded: {moduleName}"
  let data := env.header.moduleData[idx]!
  if data.isModule then
    throw <| IO.userError s!"Legacy suggestion backend requires a non-module source: {moduleName}"
  for name in data.constNames do
    unless env.getModuleIdxFor? name == some idx do
      throw <| IO.userError s!"Declaration has a different owning module: {name}"
  let importedLocalCount := env.constants.foldStage2 (fun count _ _ => count + 1) 0
  unless importedLocalCount == 0 do
    throw <| IO.userError "Imported environment unexpectedly contains local declarations"
  let current := currentModuleEnv env idx moduleName
  let localCount := current.constants.foldStage2 (fun count _ _ => count + 1) 0
  unless localCount == data.constants.size do
    throw <| IO.userError "Reconstructed local declarations do not match compiled module records"
  let required := (ImportGraph.Shake.Lean.Environment.minimalRequiredModules current).qsort
    (fun a b => a.toString < b.toString)
  let loaded := env.header.moduleNames.qsort (fun a b => a.toString < b.toString)
  return Json.mkObj [
    ("module", toJson moduleName.toString),
    ("backend", toJson "ImportGraph.Tools.MinImports"),
    ("api", toJson "ImportGraph.Shake.Lean.Environment.minimalRequiredModules"),
    ("resolved_olean", toJson olean.toString),
    ("owned_declaration_count", toJson data.constants.size),
    ("local_declaration_count", toJson localCount),
    ("compiled_direct_imports", toJson (data.imports.map (fun imp => imp.module.toString))),
    ("required_module_count", toJson required.size),
    ("required_modules", toJson (required.map Name.toString)),
    ("loaded_module_count", toJson loaded.size),
    ("loaded_modules", toJson (loaded.map Name.toString)),
    ("suggestion_only", toJson true),
    ("limitation", toJson "Declaration analysis does not account for syntax or tactics; candidate compilation and consumer coverage are required")]

public def main (args : List String) : IO UInt32 := do
  let [moduleName] := args |
    (← IO.getStderr).putStrLn "usage: legacy_import_probe MODULE"
    return 2
  let module := moduleName.toName
  if module.isAnonymous then
    (← IO.getStderr).putStrLn "Module name must be nonempty"
    return 2
  try
    IO.println (← probe module).compress
    return 0
  catch error =>
    (← IO.getStderr).putStrLn error.toString
    return 1
