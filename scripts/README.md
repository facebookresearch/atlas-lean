# Repository scripts

Run `scripts/check.sh` from the repository root. With no argument it performs
the deterministic preflight checks, enforces the library trust and dependency
policies, and builds `MathlibExt`, `CSLibExt`, `PhyslibExt`, `WantedExt`,
`MathlibExtTest`, `CSLibExtTest`, and `PhyslibExtTest`.

Use `scripts/check.sh preflight` for the fast structure and shell checks, or
`scripts/check.sh build` to build the libraries and inspect compiler diagnostics,
axiom dependencies, unsafe declarations, direct imports, and library layering.
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
