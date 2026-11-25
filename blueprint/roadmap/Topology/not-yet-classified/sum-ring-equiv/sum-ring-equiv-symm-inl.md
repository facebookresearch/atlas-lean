# Sum Ring Equiv symm inl

Recombination returns the first component function on the left summand.

Here `X,Y` are arbitrary topological spaces and `R` is a topological semiring, with independent
universes.

```lean
theorem sumRingEquiv_symm_inl (p : C(X, R) × C(Y, R)) (x : X) :
    (sumRingEquiv X Y R).symm p (Sum.inl x) = p.1 x
```
