---
article_id: af_7fb238453c050f595ddf22d4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow
---

# Residue int Trace eq nsmul trace residue of map maximal Ideal eq pow

Integral-trace residue bridge: under `map 𝔪A = 𝔪B ^ e`, the residue of
`Algebra.intTrace A B b` equals `e` times the residue-field trace of
`residue B b`. The proof combines Mathlib's quotient-trace identity
`Algebra.trace_quotient_eq_of_isDedekindDomain` (at `p := maximalIdeal A`,
whose quotient is `ResidueField A`) with the iterated quotient trace formula
`trace_residueFieldMaximalIdealPowQuotient`: since `he` collapses the defining
ideal `map 𝔪A ⊔ 𝔪B ^ e` to `map 𝔪A`, the custom quotient is
`ResidueField A`-algebra equivalent to `B ⧸ map 𝔪A` via
`Ideal.quotEquivOfEq` (fixing representatives, with scalar compatibility
checked on representatives as in
`factorResidueFieldMaximalIdealPowQuotient`), and trace conjugacy
(`Algebra.trace_eq_of_algEquiv`) transports the Mathlib identity to the
custom quotient. The DVR hypotheses supply the Dedekind and integrally-closed
instances. This is new bridge infrastructure for the corrected ATLAS N261
quotient-filtration route, not a source theorem: it controls the integral
trace only modulo `maximalIdeal A` and does not prove the wild
mixed-characteristic fractional-dual bound.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Residue Field Maximal Ideal Pow Quotient](../maximal-ideal-pow-factor/residue-field-maximal-ideal-pow-quotient.md)
- [Trace residue Field Maximal Ideal Pow Quotient](trace-residue-field-maximal-ideal-pow-qu-2.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealPowQuotientTrace](../../../../../sources/v2/MathlibExt.md)
