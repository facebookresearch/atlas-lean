# Extend By Zero apply

Zero extension retains every value at a point of the original open subspace.

The ambient space is Hausdorff, the subspace is open, and the target is an arbitrary topological
space with zero.

```lean
theorem extendByZero_apply (hs : IsOpen s) (f : C₀(s, Y)) (x : s) :
    extendByZero hs f (x : X) = f x
```
