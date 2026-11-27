# Sigma Ring Equiv apply

The component at index `i` has value `f(i,x)` at `x ∈ X(i)`.

The fibers are arbitrary topological spaces and `R` is a topological semiring; index, fiber and
coefficient universes are independent.

```lean
theorem sigmaRingEquiv_apply (f : C((Σ i, X i), R)) (i : ι) (x : X i) :
    sigmaRingEquiv X R f i x = f ⟨i, x⟩
```
