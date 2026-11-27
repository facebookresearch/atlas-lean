# Separable Space

C0 functions form a separable uniform pseudometric space when the domain is locally compact
Hausdorff second-countable and the target is separable pseudometric with zero.

```lean
theorem separableSpace (X : Type uX) (E : Type uE) [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [PseudoMetricSpace E] [Zero E] [SeparableSpace E] : SeparableSpace C₀(X, E)
```
