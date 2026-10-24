---
article_id: af_ef818d3736ebef0dd7690173
declaration: def
origin: cited
statement: formalized
lean: IsDiscreteValuationRing.residueFieldLinearEquivMaximalIdealGradedPiece
---

# Residue Field Linear Equiv Maximal Ideal Graded Piece

The `i`-th maximal-ideal graded piece is `κ`-linearly a copy of the residue
field. The underlying function and inverse come from
`Ideal.quotEquivPowQuotPowSucc`; only the residue-scalar compatibility is proved
here, by quotient induction: a residue scalar `mk r` acts on both sides as the
representative `r` acts over `R` (the maximal ideal annihilates the graded
piece, so this is well defined).

## Depends on

- [Maximal Ideal Graded Piece](maximal-ideal-graded-piece.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealGradedPiece](../../../../../sources/v2/MathlibExt.md)
