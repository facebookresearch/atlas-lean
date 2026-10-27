---
article_id: af_e848f4c491412a88b009660b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: maximalIdealPowQuotientIdeal_le
---

# Maximal Ideal Pow Quotient Ideal le

The defining ideals shrink with `n`: `map 𝔪A ⊔ 𝔪B ^ (n + 1)` is contained
in `map 𝔪A ⊔ 𝔪B ^ n`, by `Ideal.pow_le_pow_right n.le_succ` and lattice
monotonicity.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealPowFactor](../../../../../sources/v2/MathlibExt.md)
