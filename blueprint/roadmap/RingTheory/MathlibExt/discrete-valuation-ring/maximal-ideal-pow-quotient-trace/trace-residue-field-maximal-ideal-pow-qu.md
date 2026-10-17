---
article_id: af_dafb7f88752c01ef809bb995
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: trace_residueFieldMaximalIdealPowQuotient_succ
---

# Trace residue Field Maximal Ideal Pow Quotient succ

One-step trace recurrence across the maximal-ideal-power quotient tower:
the algebra trace of multiplication by the representative `b` on quotient
index `n + 1` splits as the residue-field trace of `residue B b` plus the
algebra trace of multiplication by the representative `b` on quotient index
`n`. The proof uses the factor map as the surjective intertwiner
(`map_mul` gives multiplication compatibility), identifies its kernel with
the graded piece, transports the kernel-restriction trace by conjugacy, and
applies the graded-piece trace theorem. This is new prerequisite
infrastructure for the corrected ATLAS N261 quotient-filtration route, not a
source theorem.

## Depends on

- [Maximal Ideal Graded Piece](../maximal-ideal-graded-piece/maximal-ideal-graded-piece.md)
- [Residue Field Maximal Ideal Pow Quotient](../maximal-ideal-pow-factor/residue-field-maximal-ideal-pow-quotient.md)

## Proof depends on

- [Residue Field Mul Maximal Ideal Graded Piece](../maximal-ideal-graded-piece-mul/residue-field-mul-maximal-ideal-graded-p.md)
- [Residue Field Mul Maximal Ideal Graded Piece residue mk](../maximal-ideal-graded-piece-mul/residue-field-mul-maximal-ideal-graded-p-2.md)
- [Trace residue Field Mul Maximal Ideal Graded Piece](../maximal-ideal-graded-piece-mul/trace-residue-field-mul-maximal-ideal-gr.md)
- [Trace eq trace restrict ker add of surjective](../../../../LinearAlgebra/MathlibExt/trace/invariant-submodule/trace-eq-trace-restrict-ker-add-of-surje.md)
- [Factor Residue Field Maximal Ideal Pow Quotient](../maximal-ideal-pow-factor/factor-residue-field-maximal-ideal-pow-q.md)
- [Factor Residue Field Maximal Ideal Pow Quotient surjective](../maximal-ideal-pow-factor/factor-residue-field-maximal-ideal-pow-q-2.md)
- [Residue Field Linear Equiv Maximal Ideal Graded Piece Ker Factor](../maximal-ideal-pow-factor/residue-field-linear-equiv-maximal-ideal.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealPowQuotientTrace](../../../../../sources/v2/MathlibExt.md)
