# Restrict Zero Outside apply

The restricted function retains the original value at every subspace point.

`X` is compact, `Y` is topological with zero, and the original function is zero outside `s`.

```lean
theorem restrictZeroOutside_apply (s : Set X) (f : C(X, Y))
    (hzero : ∀ x : X, x ∉ s → f x = 0) (x : s) :
    restrictZeroOutside s f hzero x = f x
```
