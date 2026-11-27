# Remaining Atlas development material

Part of [#5408](https://github.com/facebookresearch/atlas-lean/issues/5408).
The CPython and Formal Conjectures migration in
[PR #1315](https://github.com/facebookresearch/atlas-lean/pull/1315) does not
retire every development under `Atlas/`.

## StatisticalMechanics

The sources and [migration ledger](../../Atlas/StatisticalMechanics/MIGRATED.md)
remain at `Atlas/StatisticalMechanics/`. Reconcile each existing mapping with
its canonical root-library API before selecting further dependency-ordered
batches. The mathematical foundations belong in the corresponding `MathlibExt`
subjects, algorithmic material in `CSLibExt`, and physical models/results in
`PhyslibExt`. Preserve the separate physics migration in PR #893 rather than
moving its source or ledger paths in the CPython/FC batch.

The remaining prototypes, examples, conditional interfaces, and reusable results
still need per-file dispositions. Retaining these sources at their existing
paths is an interim state, not a completed archival decision or a claim that
all results are proved root-library APIs.

## CDISProbability

[`Atlas/CDISProbability/`](../../Atlas/CDISProbability/README.md) is also outside
the root Lake build. It is a separate Lean/Mathlib 4.34.0 package with `Code.*`
modules in namespace `CDIS`; it does not import the root extension libraries.
Its [notice](../../Atlas/CDISProbability/NOTICE.md), source chapters, roadmap,
and verification tooling must accompany any migration or documented archive.

Inventory at upstream main `49fb838d2859c4cd95077ad36d5948a6a953b68b`:
139 tracked files, including 17 `Code` Lean modules, three verification Lean
modules, 111 roadmap files, and the build/provenance assets. These counts are a
revision-specific inventory, not proof or migration coverage.

Disposition work still required:

- Reconcile the course statements and existing root/Mathlib providers named by
  the roadmap; do not create duplicate APIs where canonical declarations suffice.
- Select reusable probability, measure-theory, and analysis material for the
  corresponding subjects in `MathlibExt`, with focused `MathlibExtTest` clients.
  Review each statement and its hypotheses before choosing its final path.
- Replace the generic module prefix and port the selected modules to the current
  root toolchain. Preserve the `CDIS` public names where appropriate, source
  attribution, corrected course statements, and verification provenance.
- Give examples, verification tooling, and unresolved development material an
  explicit test/tooling destination or documented archival disposition. Preserve
  the immutable source references and notice; do not silently discard them.

No CDIS file is moved or newly admitted to the root build by PR #1315. Its final
module-by-module destinations or archive are pending in #5408.

## Completion boundary

Keep #5408 open until both remaining directories have documented destinations
or archival dispositions and `Atlas/` is retired as a development directory.
Approval or completion of the CPython/FC batch alone does not meet that boundary.
