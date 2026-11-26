/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Batteries.Tactic.Lint

/-!
Run environment linters on the declarations of some modules.

    lake env lean --run scripts/lint_declarations.lean ROOT MODULE...

`ROOT` is a built module that imports every `MODULE`; `scripts/check_env_linters.py` passes the
aggregator `<Library>.LintChanged` and the modules that a pull request changes. In the
environment of `ROOT`, this lints the declarations of the `MODULE`s with:

- the linters of Batteries' `#lint` that are on by default, with Mathlib's additions when `ROOT`
  imports Mathlib, as `lake exe runLinter` does;
- two that Batteries turns off by default: `docBlameThm` (a public theorem without a docstring)
  and `explicitVarsOfIff` (variables on both sides of an `↔` that should be implicit, here only
  in public declarations);
- `duplicateStatement`: a theorem whose statement another theorem of the environment already
  proves, up to the names of binders and universes. Deprecated theorems, instances and generated
  declarations are not compared;
- `rootNamespace`: a public declaration outside any namespace, with which a later Mathlib
  declaration of the same name would collide.

Like `runLinter`, it prints the findings with their file, line and column, grouped by linter and
module, and exits 1 if there is one, 0 if there is none, and 2 if it cannot run. `@[nolint X]`
keeps linter `X` off a declaration, as for `#lint`. Unlike `runLinter`, every linter lints only
the declarations of the `MODULE`s, which is what the check reports on.
-/

open Lean Core Meta Batteries.Tactic.Lint

/-- Linters that Batteries turns off by default and that this script runs as well. -/
def extraLinters : List Name := [`docBlameThm, `explicitVarsOfIff]

/-- Linters whose findings on private declarations are dropped: a private lemma is no interface. -/
def publicOnly : List Name := [`explicitVarsOfIff]

/-- `linter`, skipping private declarations if it is one of `publicOnly`. -/
def restrict (linter : NamedLinter) : NamedLinter :=
  if publicOnly.contains linter.name then
    { linter with test := fun decl => if isPrivateName decl then pure none else linter.test decl }
  else linter

/-- The statement of a theorem, with its universe parameters renamed `u_1`, `u_2`, … in order. -/
def canonicalStatement (info : ConstantInfo) : Expr :=
  let params := info.levelParams
  let canonical := (List.range params.length).map fun i => Name.mkSimple s!"u_{i + 1}"
  if params == canonical then info.type
  else info.type.instantiateLevelParams params (canonical.map Level.param)

/-- Whether the duplicate check compares the theorem `name`. -/
def comparable (env : Environment) (name : Name) (info : ConstantInfo) : Bool :=
  info matches .thmInfo _ && !env.isAutoDecl name && !Linter.isDeprecated env name

/--
For each theorem among `decls`, the other theorems of the environment that prove the same
statement (`Expr` equality ignores binder names and binder annotations).
-/
def findDuplicates (decls : Array Name) : CoreM (Std.HashMap Name (Array Name)) := do
  let env ← getEnv
  let mut statements : Std.HashMap Expr (Array Name) := {}
  for decl in decls do
    let some info := env.find? decl | continue
    unless comparable env decl info do continue
    if ← isInstance decl then continue
    let statement := canonicalStatement info
    -- A statement with no premise and no structure, such as `True`, says nothing.
    if statement.isConst then continue
    statements := statements.alter statement (·.getD #[] |>.push decl)
  if statements.isEmpty then return {}
  let record (found : Std.HashMap Name (Array Name)) (name : Name) (info : ConstantInfo) :
      Std.HashMap Name (Array Name) := Id.run do
    unless comparable env name info do return found
    let some targets := statements[canonicalStatement info]? | return found
    let mut found := found
    for target in targets do
      if target != name then
        found := found.alter target (·.getD #[] |>.push name)
    return found
  let found := env.constants.map₁.fold record {}
  return env.constants.map₂.foldl record found

/-- A theorem's name as a user writes it, with its module. -/
def describe (env : Environment) (name : Name) : String :=
  let shown := if isPrivateName name then s!"private `{privateToUserName name}`" else s!"`{name}`"
  match env.getModuleIdxFor? name >>= (env.header.moduleNames[·]?) with
  | some module => s!"{shown} (in `{module}`)"
  | none => shown

/-- The `duplicateStatement` linter, over the results of `findDuplicates`. -/
def duplicateStatement (found : Std.HashMap Name (Array Name)) : NamedLinter where
  name := `duplicateStatement
  declName := `duplicateStatement
  noErrorsFound := "No theorem restates another one."
  errorsFound := "THEOREMS WHOSE STATEMENT ANOTHER THEOREM ALREADY PROVES:"
  test declName := do
    let some others := found[declName]? | return none
    let env ← getEnv
    -- Public theorems first: they are the ones that the new theorem can use instead.
    let sorted := others.qsort fun a b =>
      (!isPrivateName a && isPrivateName b) || (isPrivateName a == isPrivateName b && a.lt b)
    let shown := (sorted.toList.take 3).map (describe env)
    let more := if sorted.size > 3 then s!", and {sorted.size - 3} more" else ""
    return m!"has the same statement as {", ".intercalate shown}{more}"

/-- The `rootNamespace` linter. -/
def rootNamespace : NamedLinter where
  name := `rootNamespace
  declName := `rootNamespace
  noErrorsFound := "No public declaration is in the root namespace."
  errorsFound := "PUBLIC DECLARATIONS IN THE ROOT NAMESPACE:"
  isLocal := true
  test declName := do
    if ← isPrivateOrAutoDecl declName then return none
    unless declName.getPrefix.isAnonymous do return none
    if ← isInstance declName then return none
    match (← getEnv).find? declName with
    | some (.thmInfo _) | some (.defnInfo _) | some (.opaqueInfo _) | some (.axiomInfo _)
    | some (.inductInfo _) =>
      return m!"is in the root namespace, where a Mathlib declaration of the same name, added \
        later, would collide with it; declare it in a namespace"
    | _ => return none

unsafe def lint (root : Name) (modules : List Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- Run the modules' initializers, which register Batteries' and Mathlib's linters.
  enableInitializersExecution
  let env ← importModules #[{ module := root }, { module := `Batteries.Tactic.Lint }] {}
    (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "", fileMap := default }
  let (code, _) ← (CoreM.toIO · ctx { env }) do
    let env ← getEnv
    let missing := modules.filter (env.getModuleIdx? · |>.isNone)
    unless missing.isEmpty do
      IO.eprintln s!"{root} does not import {missing}"
      return (2 : UInt32)
    let indices := modules.filterMap env.getModuleIdx?
    let decls := env.constants.map₁.fold (init := #[]) fun decls name _ =>
      if (env.getModuleIdxFor? name).any indices.contains then decls.push name else decls
    let linters ← getChecks (slow := true) (runOnly := none) (runAlways := some extraLinters)
    let linters := linters.map restrict ++ #[duplicateStatement (← findDuplicates decls), rootNamespace]
    let results ← lintCore decls linters (currentModule := root) (inIO := true)
    if results.all (·.2.isEmpty) then
      IO.println s!"-- Linting passed for {root}."
      return 0
    let formatted ← formatLinterResults results decls (groupByFilename := true)
      (useErrorFormat := true) s!"in {modules}" (runSlowLinters := true) .medium linters.size
    IO.print (← formatted.toString)
    return 1
  return code

unsafe def main (args : List String) : IO UInt32 := do
  let root :: modules@(_ :: _) := args.map String.toName
    | IO.eprintln "usage: lake env lean --run scripts/lint_declarations.lean ROOT MODULE..."
      return 2
  let code ← lint root modules
  -- As `runLinter` does, exit at once: Lean's finalizers can race with the lint's tasks.
  IO.Process.exit code.toUInt8
