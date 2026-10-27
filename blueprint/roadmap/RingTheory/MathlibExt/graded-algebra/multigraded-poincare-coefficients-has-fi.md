---
article_id: af_e2faea9366a9bc80c6c620dc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.multigradedPoincareCoefficients_hasFiniteSupport_of_finiteResolution
---

# Multigraded Poincare Finite Support

Finite support of the raw multigraded Poincaré-series coefficient
function from a finite-rank terminating resolution: every homogeneous
basis index type is finite, and those types are empty above `bound`.

## Depends on

- [Multigraded Base Change](multigraded-betti/multigraded-base-change.md)
- [Multigraded Free Resolution](multigraded-free-resolution/multigraded-free-resolution.md)
- [Multigraded Polynomial Module](multigraded-polynomial-module/multigraded-polynomial-module.md)
- [Multigraded Poincare Coefficients](multigraded-poincare-coefficients/multigraded-poincare-coefficients.md)

## Proof depends on

- [Multigraded Free Module](multigraded-free-resolution/multigraded-free-module.md)
- [Base Changed Complex](multigraded-betti/base-changed-complex.md)
- [Base Changed Degree Piece](multigraded-betti/base-changed-degree-piece.md)
- [Multigraded Betti Number](multigraded-betti/multigraded-betti-number.md)
- [Zero Eval](multigraded-betti/zero-eval.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport](../../../../sources/v2/MathlibExt.md)
- Benjamin Braun and Brian Davis, “Antichain Simplices,” Journal of Integer Sequences 23 (2020), `https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`, exact line 876. This is the conditional finite-resolution bridge behind that line, not the full Hilbert syzygy existence theorem: it assumes the finite terminating resolution and derives finite coefficient support, without assuming finite support, eventual Betti vanishing, or a polynomial realization, and without constructing the resolution.
