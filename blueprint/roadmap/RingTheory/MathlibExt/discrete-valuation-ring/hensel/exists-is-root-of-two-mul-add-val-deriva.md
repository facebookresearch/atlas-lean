---
article_id: af_e6e56f3438274c3891918b96
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Polynomial.exists_isRoot_of_two_mul_addVal_derivative_lt_addVal
---

# Exists is Root of two mul add Val derivative lt add Val

Strong complete-DVR Hensel endpoint: an approximate root with
   `2 * addVal (derivative) < addVal (value)` refines to an exact root `a`
   with a valuation bound, uniqueness in the strict ball, and derivative
   valuation stability. The strict-ball witness fact is kept (the ATLAS
   published statement dropped it), which is what makes uniqueness usable.
   This is an existence/uniqueness/stability statement only; it claims
   nothing about Newton sequences or convergence rates.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Add Val lt add Val add of mem maximal Ideal](add-val-lt-add-val-add-of-mem-maximal-id.md)
- [Add Val derivative eval eq of lt add Val sub](add-val-derivative-eval-eq-of-lt-add-val.md)
- [Eq of is Root of add Val derivative lt add Val sub](eq-of-is-root-of-add-val-derivative-lt-a.md)
- [Exists is Root sub mem maximal Ideal of is Unit derivative](exists-is-root-sub-mem-maximal-ideal-of.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.DiscreteValuationRing.Hensel](../../../../../sources/v2/MathlibExt.md)
