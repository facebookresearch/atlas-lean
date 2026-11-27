# Const Ring Equiv apply

The forward value is exactly the constant continuous function.

`X` has exactly one point and `R` is a topological semiring. Their universes are independent.

```lean
theorem constRingEquiv_apply (r : R) :
    constRingEquiv X R r = ContinuousMap.const X r
```
