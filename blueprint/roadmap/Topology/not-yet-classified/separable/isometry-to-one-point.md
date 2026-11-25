# Isometry to One Point

Zero extension to the one-point compactification preserves uniform distance for a pseudometric
target with zero.

`X` is R1 and `E` is a pseudometric space with zero, in independent universes.

```lean
theorem isometry_toOnePoint [PseudoMetricSpace E] [Zero E] :
    Isometry (toOnePoint : C₀(X, E) → C(OnePoint X, E))
```
