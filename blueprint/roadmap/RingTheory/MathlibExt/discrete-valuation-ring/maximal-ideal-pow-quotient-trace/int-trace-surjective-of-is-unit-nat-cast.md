---
article_id: af_752c83123dfebcf8c537bcc0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow
---

# Int Trace surjective of is Unit nat Cast of map maximal Ideal eq pow

Tame integral-trace surjectivity: under `map 𝔪A = 𝔪B ^ e` with
`IsUnit (e : B)`, the integral trace `Algebra.intTrace A B` is surjective.
Separability supplies a residue element of trace one, lifted to `b : B`;
since `e` is a unit, the bridge identity
`residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow` makes
`Algebra.intTrace A B b` a unit, and scaling `b` by an arbitrary `a` against
that unit hits every target. The `IsUnit (e : B)` form is ergonomic for the
eventual tame ramification criterion; localness makes it equivalent to
unitness in `A`. This proves the tame trace-surjectivity input only: it does
not prove the mixed-characteristic wild bound, nor ATLAS's false exact wild
equality.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Residue int Trace eq nsmul trace residue of map maximal Ideal eq pow](residue-int-trace-eq-nsmul-trace-residue.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealPowQuotientTrace](../../../../../sources/v2/MathlibExt.md)
