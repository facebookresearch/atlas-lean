# Restrict Zero Outside extend By Zero

On an open subspace of a compact Hausdorff space, restricting the zero extension recovers the
original C0 function.

`X` is compact and Hausdorff, `s` is open, and `Y` is topological with zero.

```lean
theorem restrictZeroOutside_extendByZero (hs : IsOpen s) (f : C₀(s, Y)) :
    restrictZeroOutside s (extendByZero hs f)
      (fun _x hx => extendByZero_apply_of_not_mem hs f hx) = f
```
