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
      (target == `Domains || target == `PhyslibExt || target == `CSLibExt || target == `MathlibExt))

/-- `value` with exactly `n` leading `fun` binders removed, if it has that many. -/
private def lambdaBody? (value : Lean.Expr) : Nat → Option Lean.Expr
  | 0 => some value
  | n + 1 =>
    match value with
    | .lam _ _ body _ => lambdaBody? body n
    | _ => none

/-- Whether `value` is the `T.ctorIdx` that Lean v4.36 generates for an inductive type `T` whose
number of constructors is not one: `fun params indices x => T.casesOn params (fun indices x => Nat)
indices x alt₀ … altₖ`, where alternative `i` takes the fields of constructor `i` and returns the
literal `i`. -/
private def isGeneratedCtorIdxValue (env : Lean.Environment) (info : Lean.InductiveVal)
    (value : Lean.Expr) : Bool := Id.run do
  let arity := info.numParams + info.numIndices + 1
  let some body := lambdaBody? value arity | return false
  let levels := Lean.Level.one :: info.levelParams.map Lean.mkLevelParam
  unless body.getAppFn == .const (Lean.mkCasesOnName info.name) levels do return false
  let args := body.getAppArgs
  unless args.size == arity + 1 + info.ctors.length do return false
  -- The parameters, then (after the motive) the indices and the major premise, in binder order.
  for i in [0:info.numParams] do
    unless args[i]! == .bvar (arity - 1 - i) do return false
  for j in [0:info.numIndices] do
    unless args[info.numParams + 1 + j]! == .bvar (arity - 1 - info.numParams - j) do
      return false
  unless args[arity]! == .bvar 0 do return false
  unless lambdaBody? args[info.numParams]! (info.numIndices + 1) == some (.const ``Nat []) do
    return false
  for k in [0:info.ctors.length] do
    let some (.ctorInfo ctor) := env.find? info.ctors[k]! | return false
    unless ctor.cidx == k do return false
    unless lambdaBody? args[arity + 1 + k]! ctor.numFields == some (.lit (.natVal k)) do
      return false
  return true

/-- Whether `implInfo` is the unsafe `T.ctorIdx._impl` that Lean v4.36 generates:
`fun params indices x => getObjTagNat _ x`, with the type of `T.ctorIdx`. -/
private def isGeneratedCtorIdxImpl (info : Lean.InductiveVal) (ctorIdxType : Lean.Expr) :
    Lean.ConstantInfo → Bool
  | .defnInfo impl =>
    impl.safety == .unsafe && impl.type == ctorIdxType &&
      match lambdaBody? impl.value (info.numParams + info.numIndices + 1) with
      | some body => body.isAppOfArity ``getObjTagNat 2 && body.appArg! == .bvar 0
      | none => false
  | _ => false

/-- `(T, T.ctorIdx, T.ctorIdx._impl)` for either declaration of that pair. -/
private def ctorIdxPair? : Lean.Name → Option (Lean.Name × Lean.Name × Lean.Name)
  | .str (.str t "ctorIdx") "_impl" => some (t, .str t "ctorIdx", .str (.str t "ctorIdx") "_impl")
  | .str t "ctorIdx" => some (t, .str t "ctorIdx", .str (.str t "ctorIdx") "_impl")
  | _ => none

/-- An inductive type `T` that is not a family of propositions and eliminates into `Type` gets a
compiler-generated `T.ctorIdx` (`Lean.mkCtorIdx`, in Lean's
`src/Lean/Meta/Constructions/CtorIdx.lean`). Since Lean v4.36, unless `T` has exactly one
constructor (or is a runtime builtin type), `T.ctorIdx` is `implemented_by` an unsafe
`T.ctorIdx._impl` that reads the runtime tag of its argument with `getObjTagNat`. Both are compiler
output, not library code, so the safety checks skip this pair, but only in exactly that generated
form, in the module that declares `T` and without declaration ranges (`isGeneratedCtorIdxDecl`): a
hand-written `T.ctorIdx._impl`, or a `T.ctorIdx` implemented by anything else, is still reported. -/
private def isGeneratedCtorIdx (env : Lean.Environment) (name : Lean.Name) : Bool :=
  match ctorIdxPair? name with
  | none => false
  | some (t, ctorIdx, impl) =>
    match env.find? t, env.find? ctorIdx, env.find? impl with
    | some (.inductInfo info), some (.defnInfo idx), some implInfo =>
      info.ctors.length != 1 && idx.safety == .safe &&
        Lean.Compiler.getImplementedBy? env ctorIdx == some impl &&
        (Lean.Compiler.getImplementedBy? env impl).isNone &&
        isGeneratedCtorIdxValue env info idx.value &&
        isGeneratedCtorIdxImpl info idx.type implInfo &&
        env.getModuleIdxFor? ctorIdx == env.getModuleIdxFor? t &&
        env.getModuleIdxFor? impl == env.getModuleIdxFor? t
    | _, _, _ => false

/-- Whether `name` is one of the pair Lean generated: it has the form `isGeneratedCtorIdx` checks,
and neither declaration has declaration ranges. Lean records ranges for every declaration a source
file writes, the elaborator's own auxiliary ones included, but none for what `mkCtorIdx` adds, so a
hand-written pair of exactly the generated form is still reported. Having no ranges does not prove
that Lean made a declaration: a metaprogram that adds declarations directly adds none either. Such
a pair passes only in the generated form, which reads the constructor index from the runtime tag. -/
private def isGeneratedCtorIdxDecl (name : Lean.Name) : CommandElabM Bool := do
  let some (_, ctorIdx, impl) := ctorIdxPair? name | return false
  unless isGeneratedCtorIdx (← Lean.getEnv) name do return false
  return (← Lean.findDeclarationRanges? ctorIdx).isNone &&
    (← Lean.findDeclarationRanges? impl).isNone

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
      let generated ← isGeneratedCtorIdxDecl name
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
