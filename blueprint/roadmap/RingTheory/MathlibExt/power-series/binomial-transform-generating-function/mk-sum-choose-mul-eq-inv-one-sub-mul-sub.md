---
article_id: af_562c4e4e0ef8628b21df1b32
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.mk_sum_choose_mul_eq_inv_one_sub_mul_subst
---

# Mk sum choose mul eq inv one sub mul subst

The ordinary generating function of the binomial transform `n ↦ ∑ k ≤ n, n.choose k * a k`
of a sequence `a` over a field `K` is `(1 - X)⁻¹ * (mk a).subst (X * (1 - X)⁻¹)`.
`ordinary_generating_function_binomial_transform` is the source-shaped form over `ℝ`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.RingTheory.PowerSeries.BinomialTransformGeneratingFunction](../../../../../sources/v2/MathlibExt.md)
