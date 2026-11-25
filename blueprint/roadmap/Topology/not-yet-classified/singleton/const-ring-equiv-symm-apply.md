# Const Ring Equiv symm apply

The inverse coefficient is the function value at the unique domain point.

`X` has exactly one point and `R` is a topological semiring. Their universes are independent.

```lean
theorem constRingEquiv_symm_apply (f : C(X, R)) :
    (constRingEquiv X R).symm f = f (default : X)
```
