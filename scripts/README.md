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

For the regular quality review, which scores a sample of public statements on faithfulness,
tactics, Mathlib conventions and code quality with an LLM judge, see
[`quality_review/RUBRICS.md`](quality_review/RUBRICS.md) and `scripts/quality_review.py --help`.
Its tests run in preflight; repository CI never calls the judge.

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
