---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.christol_theorem
---

# Christol theorem

Christol's theorem: algebraicity iff `p`-automaticity of coefficients.

Polynomial-relation interpretation: `IsAlgebraic (Polynomial K) f` asserts a
denominator-cleared nonzero polynomial relation over `K[X]` satisfied by `f`,
which is the formalization of algebraicity over the rational function field
`K(t)`; it is not integrality (`IsIntegral`). The right side is
`p`-automaticity (base `p`, not base `q`) of `fun n => PowerSeries.coeff n f`.
The positivity `0 < r` is preserved verbatim from the source.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.RingTheory.PowerSeries.Christol](../../../../../sources/v2/MathlibExt.md)
- Adamczewski--Bell, arXiv:1205.4091v1, lines 260--265: for `q` a positive integral power of the characteristic prime `p`, a series over `F_q` is algebraic over `F_q(t)` iff its coefficient sequence is `p`-automatic.
