# Const Ring Equiv symm to Eval Alg Hom

For commutative semiring coefficients, the inverse map is evaluation at the unique point viewed
as a semiring homomorphism.

`X` has exactly one point and `R` is a topological commutative semiring.

```lean
theorem constRingEquiv_symm_toEvalAlgHom :
    (constRingEquiv X R).symm.toRingHom =
      (ContinuousMap.evalAlgHom R R (default : X)).toRingHom
```
