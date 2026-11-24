/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Read the private import closure using explicit artifact roots and Lean's module-data API.
-/
import Lean
import Lean.Setup

open Lean

private def rawComponent : Name → String
  | .str _ value => value
  | .num _ value => toString value
  | .anonymous => ""

private def moduleComponents (module : Name) : Array String :=
  (module.components.map rawComponent).toArray

private def rootKey (module : Name) : String :=
  match module.components with
  | [] => ""
  | component :: _ => rawComponent component

private def mappedParts (module : Name) (roots : Json) : IO ImportArtifacts := do
  let candidates ← match roots.getObjValAs? (Array String) (rootKey module) with
    | .ok value => pure value
    | .error message => throw <| IO.userError s!"No selected artifact root for {module}: {message}"
  if candidates.isEmpty then
    throw <| IO.userError s!"No selected artifact root for {module}: empty candidate list"
  let mut selectedRoot := none
  for candidate in candidates do
    let candidateRoot := System.FilePath.mk candidate
    if ← (modToFilePath candidateRoot module "olean").pathExists then
      selectedRoot := some candidateRoot
      break
  let root ← match selectedRoot with
    | some value => pure value
    | none => throw <| IO.userError s!"No selected artifact root contains {module}"
  let olean := modToFilePath root module "olean"
  let (data, _) ← readModuleData olean
  let oleans := if data.isModule then
    #[olean, OLeanLevel.server.adjustFileName olean, OLeanLevel.private.adjustFileName olean]
    else #[olean]
  let irSig := modToFilePath root module "ir.sig"
  let irs ← if ← irSig.pathExists then pure #[irSig, modToFilePath root module "ir"] else pure #[]
  return .ofArrays #[oleans, irs]

private partial def visit (module : Name) (visibility : OLeanLevel)
    (arts : NameMap ImportArtifacts) (roots : Json)
    (seen : IO.Ref (Std.HashMap Name OLeanLevel)) (rows : IO.Ref (Array Json)) : IO Unit := do
  let alreadySeen := (← seen.get).contains module
  if let some previous := (← seen.get)[module]? then
    if previous ≥ visibility then return
  seen.modify fun levels => levels.insert module visibility
  let artifacts ← match arts.find? module with
    | some value => pure value
    | none => mappedParts module roots
  let oleans := artifacts.oleanParts (inServer := true)
  let parts ← readModuleDataParts oleans
  let some first := parts[0]? | throw <| IO.userError s!"No module data for {module}"
  let data ← if first.1.isModule && visibility == .private then do
    let some priv := parts[2]? | throw <| IO.userError s!"No private module data for {module}"
    pure priv.1
    else pure first.1
  unless alreadySeen do
    rows.modify fun output => output.push <| Json.mkObj [
      ("module", toJson module.toString),
      ("components", toJson (moduleComponents module)),
      ("artifacts", toJson (.ofArrays #[oleans, artifacts.irParts] : ImportArtifacts))]
  for dependency in data.imports do
    let childVisibility := if data.isModule && visibility == .private && dependency.importAll then
      .private else .exported
    visit dependency.module childVisibility arts roots seen rows

def main (args : List String) : IO UInt32 := do
  let setupPath :: rootsPath :: modules := args | return 2
  if modules.isEmpty || modules.any (fun module => module.toName.isAnonymous) then return 2
  try
    let setup ← ModuleSetup.load setupPath
    let roots ← match Json.parse (← IO.FS.readFile rootsPath) with
      | .ok value => pure value
      | .error message => throw <| IO.userError message
    let seen ← IO.mkRef ({} : Std.HashMap Name OLeanLevel)
    let rows ← IO.mkRef (#[] : Array Json)
    for module in modules do
      visit module.toName .private setup.importArts roots seen rows
    IO.println (toJson (← rows.get)).compress
    return 0
  catch error =>
    (← IO.getStderr).putStrLn error.toString
    return 1
