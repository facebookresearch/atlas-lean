# To Top Iso naturality

Naturality of `toTopIso` with respect to `f : n ⟶ m`:

`SSet.toTop.map (SSet.stdSimplex.map f)` followed by `toTopIso m`
equals `toTopIso n` followed by the induced topological simplex map
`StdSimplex.map f` (packaged as `toTopMap f`).

This is the categorical form of `SimplexCategory.toTopHomeo_naturality`,
proved by concrete extensionality in `TopCat`.
