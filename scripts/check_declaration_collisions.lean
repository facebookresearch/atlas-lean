/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lean

/-!
Import the given modules into one environment and fail unless they load together: two of
them may not declare the same name, and their initializers must run together, so two of
them may not register the same option or attribute, for example.

    lake env lean --run scripts/check_declaration_collisions.lean MODULE_LIST

`MODULE_LIST` names one module per line. `scripts/check_declaration_collisions.sh` lists
every module of the libraries the compiled audit checks, test libraries included. The audit
imports them in groups the way `lean` does, running their initializers; this check imports
all of them at once in the same way, so that no group can fail to import. The wiki's
dependency dump, `scripts/dump_v2_dependencies.lean`, imports every v2 module without
running initializers.

Two modules that never import each other each build on their own, so `lake build` cannot
see a name they both declare; only an environment that imports both can.
-/

open Lean

def main (args : List String) : IO UInt32 := do
  let [listFile] := args
    | IO.eprintln "usage: lean --run check_declaration_collisions.lean MODULE_LIST"; return 2
  let lines := (← IO.FS.lines listFile).filter (· ≠ "")
  if lines.isEmpty then
    IO.eprintln s!"FAIL [declaration collisions]: {listFile} names no module"
    return 2
  -- Lake names a module after its file path, one component per directory and file.
  -- Lean tools, the dependency dump among them, read a module name as an identifier;
  -- a path component that is not an identifier (`A-B`, `«A»`) is read as another
  -- module, or as none.
  let fromPath (module : String) : Name := (module.splitOn ".").foldl Name.mkStr .anonymous
  let misnamed := lines.filter fun module => module.toName != fromPath module
  unless misnamed.isEmpty do
    for module in misnamed do
      IO.eprintln s!"FAIL [declaration collisions]: {module.replace "." "/"}.lean: \
        every directory and file name of a module must be a Lean identifier; rename it."
    return 1
  let names := lines.map String.toName
  initSearchPath (← findSysroot)
  -- Run the modules' initializers and environment extensions, as `lean` does on import.
  unsafe enableInitializersExecution
  try
    discard <| importModules (names.map fun module => { module, importAll := true }) {}
      (trustLevel := 1024) (loadExts := true)
  catch error =>
    let message := toString error
    -- Lean reports the first collision as
    -- "import A failed, environment already contains 'X' from B".
    match message.splitOn " failed, environment already contains '" with
    | [importing, rest] =>
      match rest.splitOn "' from " with
      | [declaration, earlier] =>
        IO.eprintln s!"FAIL [declaration collisions]: {declaration} is declared in both \
          {earlier} and {importing.replace "import " ""}."
        IO.eprintln "Each module builds on its own, but no module can import both, and the \
          compiled audit imports these modules together (the wiki's dependency dump imports \
          every v2 module). Keep one declaration: import its module where the other is used, \
          and delete the copy (or rename one). A declaration that only its own test file \
          uses, such as an `exactSource` restatement, can be `private` instead."
      | _ => IO.eprintln s!"FAIL [declaration collisions]: {message}"
    | _ => IO.eprintln s!"FAIL [declaration collisions]: could not import the modules \
        together: {message}"
    return 1
  let modules := if names.size == 1 then "module imports" else "modules import"
  IO.println s!"ok [declaration collisions]: {names.size} {modules} together."
  return 0
