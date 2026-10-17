---
article_id: af_da00120200b71eaa6d803e0f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: trace_residueFieldMaximalIdealPowQuotient
---

# Trace residue Field Maximal Ideal Pow Quotient

Iterated quotient trace formula: the algebra trace of multiplication by
the representative `b` on quotient index `n` equals `n` times the
residue-field trace of `residue B b`. The proof is by induction on `n`: at
index zero the defining ideal is the whole ring so the representative is
zero, and the successor case combines the one-step recurrence
`trace_residueFieldMaximalIdealPowQuotient_succ` with the induction
hypothesis. The graded-piece module/tower hypotheses of the one-step
recurrence are installed locally from the canonical restriction of scalars
along `algebraMap (ResidueField A) (ResidueField B)`, so they do not appear
in the public signature. This is new prerequisite infrastructure for the
corrected ATLAS N261 quotient-filtration route, not a source theorem.

## Depends on

- [Residue Field Maximal Ideal Pow Quotient](../maximal-ideal-pow-factor/residue-field-maximal-ideal-pow-quotient.md)

## Proof depends on

- [Maximal Ideal Graded Piece](../maximal-ideal-graded-piece/maximal-ideal-graded-piece.md)
- [Factor Residue Field Maximal Ideal Pow Quotient](../maximal-ideal-pow-factor/factor-residue-field-maximal-ideal-pow-q.md)
- [Factor Residue Field Maximal Ideal Pow Quotient surjective](../maximal-ideal-pow-factor/factor-residue-field-maximal-ideal-pow-q-2.md)
- [Trace residue Field Maximal Ideal Pow Quotient succ](trace-residue-field-maximal-ideal-pow-qu.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealPowQuotientTrace](../../../../../sources/v2/MathlibExt.md)
