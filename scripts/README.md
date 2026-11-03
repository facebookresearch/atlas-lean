# Repository scripts

Run `scripts/check.sh` from the repository root. With no argument it performs
the deterministic preflight checks, enforces the library trust and dependency
policies, and builds `MathlibExt`, `CSLibExt`, `WantedExt`, `MathlibExtTest`,
and `CSLibExtTest`, together with every paper and note under
`Formalized Publications/`.

Use `scripts/check.sh preflight` for the fast structure and shell checks, or
`scripts/check.sh build` to build the libraries and inspect compiler diagnostics,
axiom dependencies, unsafe declarations, direct imports, and library layering.
Preflight also validates the semantic Lake target graph so the archived `v1/`
package cannot enter the root build through a glob, dependency, or extra target.
The approved `theorem_wanted` and `def_wanted` source forms are enforced in
review using `REVIEWING.md` and the pull request checklist.

`publications.py` discovers each publication's `Formalization/` directory and
includes every Lean source in the build and environment audit. It uses the
root dependency pins and a temporary Lake configuration; comparator challenges
are excluded from the normal build. See the
[publication folder requirements](../Formalized%20Publications/Readme.md#adding-a-publication).
Plain `lake build` builds the default extension targets; use `scripts/check.sh`
for the complete repository check.

For a read-only source/report inventory of the archived v1 books, see
[`INVENTORY.md`](INVENTORY.md). It records historical metadata and source
identity without scanning or compiling Lean.

For AlgebraNotes' compact, non-accepted migration ledger and identity validator,
see [`blueprint/migrations/README.md`](../blueprint/migrations/README.md).

For the reproducible, opt-in Tau Ceti quality evaluation of maintained Atlas
libraries, see [`QUALITY_EVAL.md`](QUALITY_EVAL.md). Its deterministic tests run
in preflight; model inference is never launched by repository CI.
