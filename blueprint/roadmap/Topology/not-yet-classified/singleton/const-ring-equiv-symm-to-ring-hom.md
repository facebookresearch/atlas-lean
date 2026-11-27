# Const Ring Equiv symm to Ring Hom

The inverse semiring homomorphism is evaluation at the unique point after taking the underlying
function.

`X` has exactly one point and `R` is a topological semiring. Their universes are independent.

```lean
theorem constRingEquiv_symm_toRingHom :
    (constRingEquiv X R).symm.toRingHom =
      (Pi.evalRingHom (fun _ : X => R) (default : X)).comp
        (coeFnRingHom : C(X, R) →+* (X → R))
```
