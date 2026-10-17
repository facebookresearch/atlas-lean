---
article_id: af_5e9d7ed8b5184339f2069579
declaration: structure
origin: cited
statement: formalized
lean: MetaMathlibExt.MultigradedResolutionComparison
---

# Multigraded Resolution Comparison

Comparison data between two multigraded free resolutions of the same
target: for every multidegree `α`, a chain-homotopy equivalence between the
certified degree-`α` component complexes.

A homotopy equivalence, rather than a bare quasi-isomorphism, is the
comparison-theorem input: Mathlib derives the homology isomorphism from it.
Existence and uniqueness of such a comparison are not claimed here.

## Depends on

- [Multigraded Base Change](../multigraded-betti/multigraded-base-change.md)
- [Multigraded Free Resolution](../multigraded-free-resolution/multigraded-free-resolution.md)
- [Multigraded Polynomial Module](../multigraded-polynomial-module/multigraded-polynomial-module.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.GradedAlgebra.MultigradedBettiResolutionInvariance](../../../../../sources/v2/MathlibExt.md)
