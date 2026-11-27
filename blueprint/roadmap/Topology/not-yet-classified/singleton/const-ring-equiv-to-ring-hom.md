# Const Ring Equiv to Ring Hom

For commutative semiring coefficients, the forward map is the constant algebra homomorphism
viewed as a semiring homomorphism.

`X` has exactly one point and `R` is a topological commutative semiring.

```lean
theorem constRingEquiv_toRingHom :
    (constRingEquiv X R).toRingHom = ContinuousMap.C (α := X) (R := R) (A := R)
```
