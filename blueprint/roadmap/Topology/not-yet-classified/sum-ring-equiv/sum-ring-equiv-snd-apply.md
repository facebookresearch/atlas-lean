# Sum Ring Equiv snd apply

The second restricted function has value `f(inr y)` on the right summand.

Here `X,Y` are arbitrary topological spaces and `R` is a topological semiring, with independent
universes.

```lean
theorem sumRingEquiv_snd_apply (f : C(X ⊕ Y, R)) (y : Y) :
    (sumRingEquiv X Y R f).2 y = f (Sum.inr y)
```
