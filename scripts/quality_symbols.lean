/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import Mathlib
import Lean

/-! Declaration/module provenance for generated Mathlib declarations.

Run after fetching/building the manifest-pinned dependencies:
`QUALITY_SYMBOLS_OUTPUT=/absolute/path/symbols.json lake env lean scripts/quality_symbols.lean`.
The output is an array of [declaration name, originating module] pairs.
-/

open Lean in
run_meta do
  let some output ← IO.getEnv "QUALITY_SYMBOLS_OUTPUT"
    | throwError "Set QUALITY_SYMBOLS_OUTPUT to a new output file"
  if ← System.FilePath.pathExists output then
    throwError "Symbol output already exists"
  let env ← getEnv
  let modules := env.header.moduleNames
  let mut entries : Array Json := #[]
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      entries := entries.push <| Json.arr #[Json.str name.toString,
        Json.str modules[index.toNat]!.toString]
  IO.FS.writeFile output (Json.arr entries).compress
