/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Batteries.Tactic.Alias
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
  proves, up to the names of binders and a renaming of universes. Deprecated and generated
  theorems and plain aliases are not compared, on either side, nor is a statement that is just
  `True`. An instance of the changed modules is not reported, since typeclass resolution needs it
  even where a theorem already proves its statement; a theorem that restates an instance is, since
  the instance proves it. The environment is that of `ROOT`: the changed modules and what they
  import, not the modules they do not import;
- `rootNamespace`: a public declaration outside any namespace, with which a later Mathlib
  declaration of the same name would collide.

Like `runLinter`, it prints the findings with their file, line and column, grouped by linter and
module, and exits 1 if there is one, 0 if there is none, and 2 if it cannot run. Unlike
`runLinter`, every linter lints only the declarations of the `MODULE`s, which is what the check
reports on.

`@[nolint X]` keeps one of Batteries' or Mathlib's linters off a declaration, as for `#lint`.
`duplicateStatement` and `rootNamespace` are this script's own, so Lean does not know them when it
builds a file, and `@[nolint]` cannot name them. For them, and for any linter, an entry
`["X", "Declaration.name"]` in `scripts/nolints.json`, the list of exceptions that `runLinter`
reads too, keeps linter `X` off that one declaration: a private one is named by its private name,
such as `_private.MathlibExt.Foo.0.bar`, so that an entry never matches a declaration of another
module. `python3 scripts/check_env_linters.py --check-nolints` checks the file's format.
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

/-- The exceptions file, as for `runLinter`: a JSON array of `[linter, declaration]` pairs. -/
def nolintsFile : System.FilePath := "scripts/nolints.json"

/-- The exceptions of `nolintsFile`, or none if there is no such file. -/
def readNolints : IO (Array (Name × Name)) := do
  unless ← nolintsFile.pathExists do return #[]
  match Json.parse (← IO.FS.readFile nolintsFile) >>= fromJson? with
  | .ok nolints => return nolints
  | .error error => throw <| IO.userError s!"{nolintsFile}: {error}"

/-- `results` without the findings that `nolints` lists. As for `runLinter`, an entry names one
declaration by its full name, a private one by its private name, such as
`_private.MathlibExt.Foo.0.bar`, so that it never matches a declaration of another module. -/
def dropNolints (nolints : Array (Name × Name))
    (results : Array (NamedLinter × Std.HashMap Name MessageData)) :
    Array (NamedLinter × Std.HashMap Name MessageData) :=
  results.map fun (linter, found) =>
    let listed := nolints.filterMap fun (name, decl) =>
      if name == linter.name then some decl else none
    (linter, found.filter fun decl _ => !listed.contains decl)

/-- The orders of `names`. -/
partial def orders (names : List Name) : List (List Name) :=
  if names.isEmpty then [[]]
  else names.flatMap fun name => (orders (names.erase name)).map (name :: ·)

/-- Up to this many universe parameters, `canonicalStatement` tries every renaming. -/
def maxPermutedParams : Nat := 4

/--
The statement of a theorem, with its universe parameters renamed `u_1`, `u_2`, … and its levels
normalized after (Lean orders the arguments of a `max` by universe name), so that statements that
differ only by a renaming of their universes get one key. With at most `maxPermutedParams`
parameters, it is the least (`Expr.lt`) such statement over every order of them, so any bijection
between two theorems' universes is found; with more, the order in which they first occur.
-/
def canonicalStatement (info : ConstantInfo) : Expr :=
  let params := info.levelParams
  if params.isEmpty then info.type else
  let canonical := (List.range params.length).map fun i => Level.param (.mkSimple s!"u_{i + 1}")
  let rename (order : List Name) : Expr :=
    (info.type.instantiateLevelParams order canonical).replaceLevel fun level =>
      some level.normalize
  if params.length ≤ maxPermutedParams then
    (orders params).foldl (init := rename params) fun least order =>
      let renamed := rename order
      if renamed.lt least then renamed else least
  else
    let occurring := (collectLevelParams {} info.type).params.toList
    rename (occurring ++ params.filter (!occurring.contains ·))

/--
A theorem's statement with every universe parameter replaced by `0`, which leaves only explicit
levels, so `max` and `imax` reduce to numbers. Renaming universes cannot change it, and its hash
is cached, so it finds the few theorems worth canonicalizing cheaply.
-/
def erased (info : ConstantInfo) : Expr :=
  if info.levelParams.isEmpty then info.type
  else info.type.instantiateLevelParams info.levelParams (info.levelParams.map fun _ => .zero)

/-- Whether the duplicate check compares the theorem `name`. A plain `alias` restates its target on
purpose, so it is not compared; the `mp` and `mpr` theorems of `alias ⟨a, b⟩ := h` state
implications, and are. -/
def comparable (env : Environment) (name : Name) (info : ConstantInfo) : Bool :=
  info matches .thmInfo _ && !env.isAutoDecl name && !Linter.isDeprecated env name &&
    !(Batteries.Tactic.Alias.aliasExt.find? env name matches some (.plain _))

/--
For each theorem among `decls`, the other theorems of the environment that prove the same
statement (`Expr` equality ignores binder names and binder annotations).
-/
def findDuplicates (decls : Array Name) : CoreM (Std.HashMap Name (Array Name)) := do
  let env ← getEnv
  let mut statements : Std.HashMap Expr (Array Name) := {}
  let mut erasedKeys : Std.HashSet Expr := {}
  for decl in decls do
    let some info := env.find? decl | continue
    unless comparable env decl info do continue
    -- Typeclass resolution needs an instance even where a theorem proves its statement, so an
    -- instance is not reported; a theorem that restates one is, below.
    if ← isInstance decl then continue
    let statement := canonicalStatement info
    -- `True` says nothing; a named proposition such as `def Claim : Prop := …` does.
    if statement.isConstOf ``True then continue
    statements := statements.alter statement (·.getD #[] |>.push decl)
    erasedKeys := erasedKeys.insert (erased info)
  if statements.isEmpty then return {}
  -- Cheap tests first: the environment holds hundreds of thousands of theorems.
  let record (found : Std.HashMap Name (Array Name)) (name : Name) (info : ConstantInfo) :
      Std.HashMap Name (Array Name) := Id.run do
    unless info matches .thmInfo _ do return found
    unless erasedKeys.contains (erased info) do return found
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
  let nolints ← try readNolints catch error =>
    IO.eprintln s!"{error}"
    return 2
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
    let linters :=
      linters.map restrict ++ #[duplicateStatement (← findDuplicates decls), rootNamespace]
    let results := dropNolints nolints
      (← lintCore decls linters (currentModule := root) (inIO := true))
    if results.all (·.2.isEmpty) then
      IO.println s!"-- Linting passed for {root}."
      return 0
    let formatted ← formatLinterResults results decls (groupByFilename := true)
      (useErrorFormat := true) s!"in {modules}" (runSlowLinters := true) .medium linters.size
    -- Batteries' header names `@[nolint]`, which cannot name this script's own linters.
    let mut text ← formatted.toString
    for name in [`duplicateStatement, `rootNamespace] do
      text := text.replace s!"This linter can be disabled with `@[nolint {name}]`."
        s!"This linter can be disabled for a declaration in `{nolintsFile}`."
    IO.print text
    return 1
  return code

unsafe def main (args : List String) : IO UInt32 := do
  let root :: modules@(_ :: _) := args.map String.toName
    | IO.eprintln "usage: lake env lean --run scripts/lint_declarations.lean ROOT MODULE..."
      return 2
  let code ← lint root modules
  -- As `runLinter` does, exit at once: Lean's finalizers can race with the lint's tasks.
  IO.Process.exit code.toUInt8
