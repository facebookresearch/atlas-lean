# Repository scripts

Run `scripts/check.sh` from the repository root. With no argument it performs
the deterministic preflight checks, enforces the library trust and dependency
policies, and builds `MathlibExt`, `CSLibExt`, `PhyslibExt`, `Domains`, `WantedExt`,
`MathlibExtTest`, `CSLibExtTest`, `PhyslibExtTest`, and `DomainsTest`.

Use `scripts/check.sh preflight` for the fast structure and shell checks, or
`scripts/check.sh build` to build the libraries and inspect compiler diagnostics,
axiom dependencies, unsafe declarations, direct imports, and library layering.
The build checks also import every module of the nine libraries that the compiled audit
checks into one environment, running their initializers
(`scripts/check_declaration_collisions.sh`); the blueprint's dependency dump imports
every module of `MathlibExt`, `CSLibExt`, `PhyslibExt`, `Domains`, and `WantedExt`
without running initializers. Both take their module list from
`scripts/list_v2_modules.sh`. Two modules that never import each other each build on
their own even when they declare the same name; when Lean refuses to load them
together, this check fails and prints Lean's error. Keep one declaration and import its
module where the other was used, or make a declaration that only its own test file uses
`private`. The check also rejects a module whose directory or file name is not a Lean
identifier, since Lean tools cannot import such a module by name, and a source path that
Git tracks but the audit's directory walk does not find, or the reverse.
The build checks run in this order: the build with its compiler diagnostics, this
collision check, then the compiled audit of trust and dependency policies, which takes
longer than the collision check. Every check runs and every failure is reported, unless
`ATLAS_CHECK_FAIL_FAST=1`, which CI sets for merge groups: `scripts/check.sh` then stops
at the first failing check.
With `ATLAS_TOOL_TESTS=skip`, `scripts/test_scripts.sh` leaves out the nine tool test suites at
its end, whose tests read only scripts, workflows and the pins. CI sets it only on a pull request
whose every changed path is graph data, documentation, a Lean file of the nine libraries or under
`provenance/` (`scripts/ci_scope.py`); every other run, merge groups and pushes included, runs
them.
The compiled audit runs its batches in parallel, as many as the available memory
holds at 6 GiB each; on a shared machine, `ATLAS_AUDIT_WORKERS=N` sets the count
(`1` runs them one after another).
Preflight also validates the semantic Lake target graph so the archived `v1/`
package cannot enter the root build through a glob, dependency, or extra target.
The approved `theorem_wanted` and `def_wanted` source forms are enforced in
review using `REVIEWING.md` and the pull request checklist.

For a read-only source/report inventory of the archived v1 books, see
[`INVENTORY.md`](INVENTORY.md). It records historical metadata and source
identity without scanning or compiling Lean.

For AlgebraNotes' compact, non-accepted migration ledger and identity validator,
see [`blueprint/migrations/README.md`](../blueprint/migrations/README.md).

For the reproducible, opt-in Tau Ceti quality evaluation of maintained Atlas
libraries, see [`QUALITY_EVAL.md`](QUALITY_EVAL.md). Its deterministic tests run
in preflight; model inference is never launched by repository CI.

For the Formal-Math sync manifest, its offline checker (run by preflight on
files synced from Formal-Math), the divergence helper and the refresh script, see
[`provenance/README.md`](../provenance/README.md).

For opt-in import optimization, see [`import_optimizer/README.md`](import_optimizer/README.md).
The inventory generator and optimizer use the pinned Lean tools, compile isolated
candidates, and compare owned declarations before saving patches. They never apply
those patches to library sources. Python regressions run in preflight; native
optimization and its smoke test are explicit commands, not CI-wide import rewrites.

## Linter checks

`.github/workflows/linters.yml` (`mathlib linters`) reports Lean's, Batteries' and Mathlib's
linters on the code a pull request adds, so code already on `main` never shows up. It builds the
changed Lean files of the five production libraries once
(`scripts/lean_changes.py build --base <ref>`), then runs:

- `scripts/check_syntax_linters.py`: on added lines, the warnings of every linter the build runs,
  read with `lake lint` (Mathlib's standard set, which `lakefile.toml` turns on, and the linters
  that Lean, Batteries and Mathlib turn on by default), and the deprecation warnings that Lake
  replays from the build log;
- `scripts/check_env_linters.py`: the findings of `#lint`'s environment linters (`runLinter`) on
  the declarations the change adds. A declaration counts as added when the change adds the line
  that declares it, below its docstring and attributes, and no declaration of that name is in the
  changed files at the base (for a private declaration, including a `module` file's declarations
  outside a `public section` that are not marked `public`, in its own file), so documenting,
  tagging, editing or moving an existing declaration does not report it. A `theorem_wanted` or
  `def_wanted` statement is not the declaration that proves it, so a proof's findings are reported;
- `scripts/check_text_linters.py`: Mathlib's `lint-style` errors on added lines, and the module
  names of added or renamed files;
- `scripts/check_unused_imports.py`: the added import lines that
  [agitate](https://github.com/thorimur/agitate), a faster reimplementation of `lake shake`, would
  remove. Module files are checked with `--keep-public --add-public --keep-implied --keep-prefix`,
  other files with `agitate-nonmodule --keep-implied --keep-prefix`. It never applies a removal:
  one can need the smaller imports that agitate suggests adding in its place, which the finding
  names. The workflow builds agitate from a pinned commit, which must match `lean-toolchain`;
  locally, pass a built checkout with `--agitate-dir` or `AGITATE_DIR`. A changed file whose header
  agitate cannot read, and so skips, makes it exit 2: the check is incomplete.

Each takes `--base <ref>` and exits 1 on a finding, 0 with `--report-only` (as CI runs them),
and 2 when it cannot run. `scripts/linters_self_test.py` runs them all on a probe module; CI
runs it when a pull request changes them, `lean-toolchain` or `lake-manifest.json`, so that a
bump that changes what the tools print shows up on the bump itself.
