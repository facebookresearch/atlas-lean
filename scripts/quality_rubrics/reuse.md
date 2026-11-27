# Reuse and generality

Does the declaration build on Mathlib and ATLAS instead of rebuilding them, and is it
stated so that others can reuse it?

Check, searching the pinned Mathlib sources and the ATLAS libraries:

- **Duplication**: the same statement, or a one- or two-line consequence of a single
  existing declaration, already exists in Mathlib, Batteries, Lean core, CSLib,
  Physlib or elsewhere in ATLAS. Name the existing declaration and its module.
- **Parallel definitions**: a new definition equivalent to an existing one (a custom
  "group of divisors", "finite measure", "Lipschitz constant") instead of the
  library notion, or a structure bundling data Mathlib keeps unbundled.
- **Thin wrappers**: an `abbrev` or theorem whose only content is renaming or
  specialising a library declaration, then re-proving lemmas about it.
- **Removable hypotheses**: a hypothesis that can be deleted outright (see
  `removable_hypothesis`); typeclass assumptions stronger than used (`Field` where
  `CommRing` suffices, `[Fintype]` where `[Finite]` suffices).
- **Interface**: is there a small reusable API (characterisation lemmas, `simp`
  lemmas, basic instances) so a downstream user does not have to unfold the
  definition?

Anchors:

- 5: new, at the natural generality, built from library notions, with a usable API.
- 4: new and reusable; slightly over-specialised or a minor redundant assumption.
- 3: partly duplicates library material, or noticeably stronger assumptions than needed.
- 2: a parallel definition or a re-proof of an existing library result.
- 1: an exact duplicate, or a wrapper whose only purpose is to restate a library declaration.
