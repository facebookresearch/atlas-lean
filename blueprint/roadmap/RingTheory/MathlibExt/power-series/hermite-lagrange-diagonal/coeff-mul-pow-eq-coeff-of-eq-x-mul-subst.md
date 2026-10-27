---
article_id: af_b5bb02c8da5a507f96f7bca0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.LagrangeInversion.coeff_mul_pow_eq_coeff_of_eq_X_mul_subst
---

# Coeff mul pow eq coeff of eq X mul subst

Hermite's diagonal form of Lagrange inversion without side conditions: if `w = X * φ(w)` and
`(1 - X * φ'(w)) * G = F(w)`, then `coeff n (F * φ ^ n) = coeff n G`. The constant term of `w`
vanishes automatically, and `φ` may have zero constant term.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.RingTheory.PowerSeries.HermiteLagrangeDiagonal](../../../../../sources/v2/MathlibExt.md)
