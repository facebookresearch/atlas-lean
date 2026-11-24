# Repository scripts

Run `scripts/check.sh` from the repository root. With no argument it performs
the deterministic preflight checks, enforces the library trust and dependency
policies, and builds `MathlibExt`, `CSLibExt`, `PhyslibExt`, `Domains`, `WantedExt`,
`MathlibExtTest`, `CSLibExtTest`, `PhyslibExtTest`, and `DomainsTest`.

Use `scripts/check.sh preflight` for the fast structure and shell checks, or
`scripts/check.sh build` to build the libraries and inspect compiler diagnostics,
axiom dependencies, unsafe declarations, direct imports, and library layering.
The build checks also import every module of `MathlibExt`, `CSLibExt`, `PhyslibExt`,
`Domains`, and `WantedExt` into one environment, as the blueprint's dependency dump
does (`scripts/check_declaration_collisions.sh`; both take their module list from
`scripts/list_v2_modules.sh`). Two modules that never import each other each build on
their own even when they declare the same name; this check fails on such a collision
and names the declaration and both modules. Keep one declaration and import its module
where the other was used. It also rejects a module whose directory or file name is not
a Lean identifier, since Lean tools cannot import such a module by name.
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
