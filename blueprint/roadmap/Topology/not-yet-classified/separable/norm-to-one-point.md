# Norm to One Point

Zero extension to the one-point compactification preserves the original C0 supremum norm.

`X` is R1 and `E` is a normed additive commutative group, in independent universes.

```lean
theorem norm_toOnePoint [NormedAddCommGroup E] (f : C₀(X, E)) :
    ‖f.toOnePoint‖ = ‖f‖
```
