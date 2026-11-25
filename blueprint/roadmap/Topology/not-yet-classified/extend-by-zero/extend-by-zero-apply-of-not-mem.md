# Extend By Zero apply of not mem

Zero extension has value zero at every point outside the open subspace.

The ambient space is Hausdorff, the subspace is open, and the target is an arbitrary topological
space with zero.

```lean
theorem extendByZero_apply_of_not_mem (hs : IsOpen s) (f : C₀(s, Y))
    {x : X} (hx : x ∉ s) : extendByZero hs f x = 0
```
