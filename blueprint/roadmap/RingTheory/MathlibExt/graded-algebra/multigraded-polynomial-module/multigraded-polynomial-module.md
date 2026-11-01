---
article_id: af_7a12ee9a515c8bfb1225002a
declaration: structure
origin: cited
statement: formalized
lean: MetaMathlibExt.MultigradedPolynomialModule
---

# Multigraded Polynomial Module

A `ℤⁿ`-graded module over `MvPolynomial (Fin n) K` with the standard
monomial degree-shift action: each homogeneous piece is a `K`-submodule, the
pieces give a direct-sum decomposition of `M`, scalars act through
`MvPolynomial.C`, and multiplication by `monomial a c` sends the `α`-piece
into the `(α + natDegreeToInt a)`-piece.

This records only the graded object. It does not provide resolutions,
Betti numbers, or any polynomiality conclusion; see the module docstring.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.RingTheory.GradedAlgebra.MultigradedPolynomialModule](../../../../../sources/v2/MathlibExt.md)
