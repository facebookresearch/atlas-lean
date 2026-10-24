---
article_id: af_20b049e1c8f541ec10d5c392
declaration: def
origin: cited
statement: formalized
lean: residueFieldLinearEquivMaximalIdealGradedPieceKerFactor
---

# Residue Field Linear Equiv Maximal Ideal Graded Piece Ker Factor

The `n`-th maximal-ideal graded piece of `B` is `ResidueField A`-linearly
the kernel of the factor map from index `n + 1` to index `n`, when
`map 𝔪A ≤ 𝔪B ^ (n + 1)`. The map sends a graded representative to the
corresponding quotient representative, which lies in the kernel because the
representative lies in `𝔪B ^ n`. Bijectivity goes through the quotient-ring
equivalence `residueFieldMaximalIdealPowQuotientEquivPow` (replacing the source
ideal by `𝔪B ^ (n + 1)`), `Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow`, and
`Ideal.Quotient.factor_ker`. Residue-base scalar compatibility is checked on
representatives via the scalar tower through `ResidueField B` (there is no
`ResidueField A`-algebra structure on `B`). This is new supporting
infrastructure for the corrected ATLAS N261 quotient-filtration route, not a
source theorem.

## Depends on

- [Maximal Ideal Graded Piece](../maximal-ideal-graded-piece/maximal-ideal-graded-piece.md)
- [Residue Field Maximal Ideal Pow Quotient](residue-field-maximal-ideal-pow-quotient.md)
- [Factor Residue Field Maximal Ideal Pow Quotient](factor-residue-field-maximal-ideal-pow-q.md)

## Proof depends on

- [Factor Residue Field Maximal Ideal Pow Quotient mk](factor-residue-field-maximal-ideal-pow-q-3.md)
- [Residue Field Maximal Ideal Pow Quotient Equiv Pow](residue-field-maximal-ideal-pow-quotient-2.md)
- [Residue Field Maximal Ideal Pow Quotient Equiv Pow mk](residue-field-maximal-ideal-pow-quotient-3.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealPowFactor](../../../../../sources/v2/MathlibExt.md)
