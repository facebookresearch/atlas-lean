# Const Ring Equiv comp Left Continuous

Singleton coefficient equivalences commute with continuous semiring-homomorphism
postcomposition, in independent coefficient universes.

`X` has exactly one point; `R,S` are topological semirings and the displayed semiring homomorphism
is continuous.

```lean
theorem constRingEquiv_compLeftContinuous (f : R →+* S) (hf : Continuous f) :
    (f.compLeftContinuous X hf).comp (constRingEquiv X R).toRingHom =
      (constRingEquiv X S).toRingHom.comp f
```
