# Eval app pre app ihom Vertex Equiv

The vertex of `nerve D` obtained by evaluating a map `m : Z ⟶ nerve D`
at a vertex `z` of `Z` through the internal-hom evaluation at `Δ[0]`:
precomposition with `const z` followed by `(SSet.evalDeltaZeroIso _).hom`
recovers `m.app _ z`.
