# Sum Ring Equiv symm inr

Recombination returns the second component function on the right summand.

Here `X,Y` are arbitrary topological spaces and `R` is a topological semiring, with independent
universes.

```lean
theorem sumRingEquiv_symm_inr (p : C(X, R) × C(Y, R)) (y : Y) :
    (sumRingEquiv X Y R).symm p (Sum.inr y) = p.2 y
```
