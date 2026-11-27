# Sum Ring Equiv fst apply

The first restricted function has value `f(inl x)` on the left summand.

Here `X,Y` are arbitrary topological spaces and `R` is a topological semiring, with independent
universes.

```lean
theorem sumRingEquiv_fst_apply (f : C(X ⊕ Y, R)) (x : X) :
    (sumRingEquiv X Y R f).1 x = f (Sum.inl x)
```
