---
article_id: af_f29d66fadbfd7eb5c4158048
declaration: def
origin: cited
statement: formalized
lean: factorResidueFieldMaximalIdealPowQuotient
---

# Factor Residue Field Maximal Ideal Pow Quotient

The canonical `ResidueField A`-algebra factor map from index `n + 1` to
index `n`. The underlying ring hom is `Ideal.Quotient.factor` for the
containment `maximalIdealPowQuotientIdeal_le`; scalar compatibility is by
quotient induction on a residue-field representative (both algebra maps send
`⟦a⟧` to `⟦algebraMap A B a⟧`, definitionally).

## Depends on

- [Residue Field Maximal Ideal Pow Quotient](residue-field-maximal-ideal-pow-quotient.md)

## Proof depends on

- [Maximal Ideal Pow Quotient Ideal le](maximal-ideal-pow-quotient-ideal-le.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealPowFactor](../../../../../sources/v2/MathlibExt.md)
