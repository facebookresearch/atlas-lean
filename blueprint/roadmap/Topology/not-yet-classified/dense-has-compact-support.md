# Compact Support Density

Compactly supported complex C0 functions are dense in the original supremum norm.

The domain is locally compact and Hausdorff; no countability or nonempty-set assumption is imposed.

```lean
theorem dense_hasCompactSupport : Dense {g : C₀(X, ℂ) | HasCompactSupport g}
```
