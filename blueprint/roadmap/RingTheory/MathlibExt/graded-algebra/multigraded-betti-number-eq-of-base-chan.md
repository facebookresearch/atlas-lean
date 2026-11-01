---
article_id: af_224854db52e00c76694f5094
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.multigradedBettiNumber_eq_of_baseChange
---

# Multigraded Betti Invariance

For one fixed multigraded free resolution, the multigraded Betti number is
independent of the certified component-presentation package: any two
`MultigradedBaseChange` presentations give the same `multigradedBettiNumber`
in every multidegree `α` and homological index `i`.

## Depends on

- [Multigraded Base Change](multigraded-betti/multigraded-base-change.md)
- [Multigraded Free Resolution](multigraded-free-resolution/multigraded-free-resolution.md)
- [Multigraded Polynomial Module](multigraded-polynomial-module/multigraded-polynomial-module.md)
- [Multigraded Betti Number](multigraded-betti/multigraded-betti-number.md)

## Proof depends on

- [Base Changed Complex](multigraded-betti/base-changed-complex.md)
- [Base Changed Degree Piece](multigraded-betti/base-changed-degree-piece.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.GradedAlgebra.MultigradedBettiInvariance](../../../../sources/v2/MathlibExt.md)
- Benjamin Braun and Brian Davis, “Antichain Simplices,” Journal of Integer Sequences 23 (2020), `https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`, exact lines 866--874. This covers only the fixed-resolution coherence step; independence across resolutions, finite support, Poincaré polynomiality, and Hilbert syzygy are deliberately not claimed here.
