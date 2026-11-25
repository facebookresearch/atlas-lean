# Coe const Ring Equiv

The whole forward function is the constant-function constructor.

`X` has exactly one point and `R` is a topological semiring. Their universes are independent.

```lean
theorem coe_constRingEquiv :
    (constRingEquiv X R : R → C(X, R)) = ContinuousMap.const X
```
