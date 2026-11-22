/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Batteries.Util.ProofWanted
import Lean.Compiler.ImplementedByAttr
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean.Elab.Command

private def trustedAxioms : Array Lean.Name :=
  #[``propext, ``Quot.sound, ``Classical.choice]

private def libraryRoots : Array Lean.Name :=
  #[`CSLibExt, `CSLibExtTest, `MathlibExt, `MathlibExtTest, `PhyslibExt, `PhyslibExtTest,
    `Domains, `DomainsTest, `WantedExt]

private def libraryOf? (name : Lean.Name) : Option Lean.Name :=
  libraryRoots.find? (·.isPrefixOf name)

private def mayImport (source target : Lean.Name) : Bool :=
  (source == `CSLibExt && target == `MathlibExt) ||
    (source == `CSLibExtTest && (target == `CSLibExt || target == `MathlibExt)) ||
    (source == `MathlibExtTest && target == `MathlibExt) ||
    (source == `PhyslibExt && (target == `CSLibExt || target == `MathlibExt)) ||
    (source == `PhyslibExtTest &&
      (target == `PhyslibExt || target == `CSLibExt || target == `MathlibExt)) ||
    (source == `Domains && (target == `PhyslibExt || target == `CSLibExt || target == `MathlibExt)) ||
    (source == `DomainsTest &&
      (target == `Domains || target == `PhyslibExt || target == `CSLibExt || target == `MathlibExt)) ||
    (source == `WantedExt &&
      (target == `CSLibExt || target == `MathlibExt))

/-- Since Lean v4.36, every inductive type `T` gets a compiler-generated `T.ctorIdx` that is
`implemented_by` an unsafe `T.ctorIdx._impl`. Both are compiler output, not library code, so the
safety checks skip exactly this pair. -/
private def isGeneratedCtorIdx (env : Lean.Environment) (name : Lean.Name) : Bool :=
  let isInductive (n : Lean.Name) : Bool :=
    match env.find? n with
    | some (.inductInfo _) => true
    | _ => false
  match name with
  | .str (.str t "ctorIdx") "_impl" => isInductive t
  | .str t "ctorIdx" =>
    isInductive t && Lean.Compiler.getImplementedBy? env name == some (name ++ `_impl)
  | _ => false

private def containsWantedWrapper (type : Lean.Expr) : Bool :=
  (type.find? fun
    | .const name _ =>
      name == ``ProofWanted || name == ``DefWanted || name == ``DerivedWanted
    | _ => false).isSome

run_cmd do
  let env ← Lean.getEnv
  let mut failed := false

  for i in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]!
    let some library := libraryOf? moduleName | continue
    let moduleData := env.header.moduleData[i]!

    for imported in moduleData.imports do
      let some importedLibrary := libraryOf? imported.module | continue
      if importedLibrary != library && !mayImport library importedLibrary then
        Lean.logError m!"{moduleName} must not import {imported.module}"
        failed := true

    let mut hasWantedDeclaration := false
    for name in moduleData.constNames do
      let some info := env.find? name | continue
      let generated := isGeneratedCtorIdx env name
      if info.isUnsafe && !generated then
        Lean.logError m!"{name} is an unsafe declaration"
        failed := true
      if (Lean.Compiler.getImplementedBy? env name).isSome && !generated then
        Lean.logError m!"{name} uses implemented_by"
        failed := true
      if containsWantedWrapper info.type then
        hasWantedDeclaration := true

      let axioms ← Lean.collectAxioms name
      let forbidden :=
        (axioms.filter fun ax => !trustedAxioms.contains ax).qsort Lean.Name.quickLt
      unless forbidden.isEmpty do
        Lean.logError m!"{name} depends on forbidden axioms: {forbidden}"
        failed := true

    if hasWantedDeclaration then
      if library != `WantedExt then
        Lean.logError m!"{moduleName} contains a wanted declaration outside WantedExt"
        failed := true
      unless moduleData.imports.any (·.module == `Batteries.Util.ProofWanted) do
        Lean.logError m!"{moduleName} must directly import Batteries.Util.ProofWanted"
        failed := true

  if failed then
    throwError
      "audited libraries violate the axiom, safety, wanted-declaration, or import policy"
