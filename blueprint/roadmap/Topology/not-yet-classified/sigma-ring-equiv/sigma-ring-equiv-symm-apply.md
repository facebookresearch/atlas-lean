# Sigma Ring Equiv symm apply

Recombining the family has value `f(i)(x)` at the sigma point `(i,x)`.

The fibers are arbitrary topological spaces and `R` is a topological semiring; index, fiber and
coefficient universes are independent.

```lean
theorem sigmaRingEquiv_symm_apply (f : ∀ i, C(X i, R)) (i : ι) (x : X i) :
    (sigmaRingEquiv X R).symm f ⟨i, x⟩ = f i x
```
