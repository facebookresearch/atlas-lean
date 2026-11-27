# Extend By Zero restrict Zero Outside

On an open subspace of a compact Hausdorff space, zero extension after restriction recovers a
function supported there.

`X` is compact and Hausdorff, `s` is open, and `Y` is topological with zero.

```lean
theorem extendByZero_restrictZeroOutside (hs : IsOpen s) (f : C(X, Y))
    (hzero : ∀ x : X, x ∉ s → f x = 0) :
    extendByZero hs (restrictZeroOutside s f hzero) = f
```
