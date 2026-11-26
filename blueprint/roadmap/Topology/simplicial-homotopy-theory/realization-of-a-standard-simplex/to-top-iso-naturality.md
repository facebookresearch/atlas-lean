# Naturality of the standard-simplex realization

For `n, m : SimplexCategory` and `f : n ⟶ m`, the canonical realization isomorphisms commute with the induced simplex maps:
`SSet.toTop.map (stdSimplex.map f) ≫ (toTopIso m).hom = (toTopIso n).hom ≫ toTopMap f`.
Both sides are morphisms from the realization of `stdSimplex.obj n` to the real standard simplex on `Fin (m.len + 1)`.
