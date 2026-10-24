---
article_id: af_a680362b35ecd8b322d4f67a
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.multigradedPoincarePolynomial
---

# Multigraded Poincare Polynomial

Multigraded Poincaré polynomial: the raw coefficient family
`multigradedPoincareCoefficients data`, packaged as an
`AddMonoidAlgebra` element over homological degree times multidegree.

This is conditional on the finite terminating resolution: every
homogeneous basis index type is finite (`finiteBasis`), and those types
are empty above `bound` (`emptyAbove`). Edge 6 turns exactly these two
hypotheses into finite support; the polynomial adds no further
mathematics.

## Depends on

- [Multigraded Base Change](../multigraded-betti/multigraded-base-change.md)
- [Multigraded Free Resolution](../multigraded-free-resolution/multigraded-free-resolution.md)
- [Multigraded Polynomial Module](../multigraded-polynomial-module/multigraded-polynomial-module.md)

## Proof depends on

- [Multigraded Poincare Coefficients](../multigraded-poincare-coefficients/multigraded-poincare-coefficients.md)
- [Multigraded Poincare Finite Support](../multigraded-poincare-coefficients-has-fi.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial](../../../../../sources/v2/MathlibExt.md)
