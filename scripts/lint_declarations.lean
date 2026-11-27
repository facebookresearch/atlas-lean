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
module. `--check-nolints [FILE]` only reads the file (by default `scripts/nolints.json`) as the
lint does, and exits 2 if it cannot; the workflow runs it on a pull request that changes the file.
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

/-- The exceptions of `file`, or none if there is no such file. -/
def readNolints (file : System.FilePath := nolintsFile) : IO (Array (Name × Name)) := do
  unless ← file.pathExists do return #[]
  match Json.parse (← IO.FS.readFile file) >>= fromJson? with
  | .ok nolints => return nolints
  | .error error => throw <| IO.userError s!"{file}: {error}"

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

/-- The arguments of nested `max`es. -/
partial def maxArgs : Level → List Level
  | .max a b => maxArgs a ++ maxArgs b
  | level => [level]

/-- A bijection between some universe parameters of two statements, both ways. -/
abbrev Renaming := Std.HashMap Name Name × Std.HashMap Name Name

/-- `ρ` with `m` mapped to `n`, if it stays a bijection. -/
def Renaming.extend (ρ : Renaming) (m n : Name) : Option Renaming :=
  match ρ.1[m]?, ρ.2[n]? with
  | some n', some m' => if n' == n && m' == m then some ρ else none
  | none, none => some (ρ.1.insert m n, ρ.2.insert n m)
  | _, _ => none

/-- A search continues with `k` from each renaming that a match allows, until `k` succeeds. -/
abbrev Continue := Renaming → Option Renaming

mutual
  /-- Match the level `a` with `b`, the arguments of a `max` in any order, extending `ρ`. -/
  partial def matchLevel (ρ : Renaming) (a b : Level) (k : Continue) : Option Renaming :=
    match a, b with
    | .zero, .zero => k ρ
    | .succ a, .succ b => matchLevel ρ a b k
    | .param m, .param n => (ρ.extend m n).bind k
    | .max .., .max .. => matchLevelsInAnyOrder ρ (maxArgs a) (maxArgs b) k
    | .imax a₁ a₂, .imax b₁ b₂ => matchLevel ρ a₁ b₁ fun ρ => matchLevel ρ a₂ b₂ k
    | _, _ => none

  /-- Match the levels `as` with the levels `bs` in some order, extending `ρ`. -/
  partial def matchLevelsInAnyOrder (ρ : Renaming) (as bs : List Level) (k : Continue) :
      Option Renaming :=
    match as with
    | [] => if bs.isEmpty then k ρ else none
    | a :: as => Id.run do
      for i in [0:bs.length] do
        if let some ρ := matchLevel ρ a bs[i]! fun ρ => matchLevelsInAnyOrder ρ as (bs.eraseIdx i) k
        then
          return some ρ
      return none
end

/-- The pairs of levels that a walk of two statements has met so far, and the pairs of subterms it
has walked, which it does not walk again. -/
abbrev LevelPairs := StateT (Std.HashSet (Level × Level) × Std.HashSet (Expr × Expr)) Option

/-- Walk `a` and `b` together, failing where they differ by more than the names and annotations of
binders and their levels, and record each pair of levels at the same place, normalized (Lean
orders the arguments of a `max` by universe name). Each pair of subterms is walked once, so a
statement whose subterms are shared is not walked as a tree, and the recursion is as deep as the
statements, not as large. -/
partial def levelPairs (a b : Expr) : LevelPairs Unit := do
  if (← get).2.contains (a, b) then return
  modify fun (levels, walked) => (levels, walked.insert (a, b))
  let add (u v : Level) : LevelPairs Unit :=
    modify fun (levels, walked) => (levels.insert (u.normalize, v.normalize), walked)
  match a, b with
  | .bvar i, .bvar j => unless i == j do failure
  | .sort u, .sort v => add u v
  | .const m us, .const n vs =>
    unless m == n && us.length == vs.length do failure
    for (u, v) in us.zip vs do add u v
  | .app f x, .app g y => levelPairs f g; levelPairs x y
  | .lam _ t x _, .lam _ s y _ => levelPairs t s; levelPairs x y
  | .forallE _ t x _, .forallE _ s y _ => levelPairs t s; levelPairs x y
  | .letE _ t v x _, .letE _ s w y _ => levelPairs t s; levelPairs v w; levelPairs x y
  | .lit l, .lit l' => unless l == l' do failure
  | .proj s i x, .proj t j y => unless s == t && i == j do failure; levelPairs x y
  | .mdata _ x, _ => levelPairs x b
  | _, .mdata _ y => levelPairs a y
  | .fvar x, .fvar y => unless x == y do failure
  | .mvar x, .mvar y => unless x == y do failure
  | _, _ => failure

/-- Whether some bijection between universe parameters maps the first level of each of `pairs`
to its second, the arguments of each `max` in any order. Only the choices for a `max` are
backtracked over, and the search is as deep as the levels of `pairs` are large together. -/
partial def bijective (ρ : Renaming) : List (Level × Level) → Option Renaming
  | [] => some ρ
  | (u, v) :: pairs => matchLevel ρ u v fun ρ => bijective ρ pairs

/-- Whether the statements `a` and `b` are equal up to the names and annotations of binders and
some bijection between their universe parameters. -/
def sameStatement (a b : Expr) : Bool :=
  match (levelPairs a b).run ({}, {}) with
  | some ((), (levels, _)) => (bijective ({}, {}) levels.toList).isSome
  | none => false

/--
A theorem's statement with every universe parameter replaced by `0`, which leaves only explicit
levels, so `max` and `imax` reduce to numbers. Renaming universes cannot change it, and its hash
is cached, so it finds the few theorems worth matching with `sameStatement` cheaply.
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
statement, as `sameStatement` decides.
-/
def findDuplicates (decls : Array Name) : CoreM (Std.HashMap Name (Array Name)) := do
  let env ← getEnv
  -- The theorems to report on, with their statements, by their statements with universes erased.
  let mut statements : Std.HashMap Expr (Array (Name × Expr)) := {}
  for decl in decls do
    let some info := env.find? decl | continue
    unless comparable env decl info do continue
    -- Typeclass resolution needs an instance even where a theorem proves its statement, so an
    -- instance is not reported; a theorem that restates one is, below.
    if ← isInstance decl then continue
    -- `True` says nothing; a named proposition such as `def Claim : Prop := …` does.
    if info.type.isConstOf ``True then continue
    statements := statements.alter (erased info) (·.getD #[] |>.push (decl, info.type))
  if statements.isEmpty then return {}
  -- Cheap tests first: the environment holds hundreds of thousands of theorems.
  let record (found : Std.HashMap Name (Array Name)) (name : Name) (info : ConstantInfo) :
      Std.HashMap Name (Array Name) := Id.run do
    unless info matches .thmInfo _ do return found
    let some targets := statements[erased info]? | return found
    unless comparable env name info do return found
    let mut found := found
    for (target, statement) in targets do
      if target != name && sameStatement statement info.type then
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
  if let "--check-nolints" :: rest := args then
    -- Read the exceptions file as `lint` does, and only that.
    let file : System.FilePath := rest.head?.getD nolintsFile.toString
    try
      IO.println s!"{file} lists {(← readNolints file).size} exception(s)."
      return 0
    catch error =>
      IO.eprintln s!"{error}"
      return 2
  let root :: modules@(_ :: _) := args.map String.toName
    | IO.eprintln "usage: lake env lean --run scripts/lint_declarations.lean ROOT MODULE...\n\
        or:    lake env lean --run scripts/lint_declarations.lean --check-nolints [FILE]"
      return 2
  let code ← lint root modules
  -- As `runLinter` does, exit at once: Lean's finalizers can race with the lint's tasks.
  IO.Process.exit code.toUInt8
