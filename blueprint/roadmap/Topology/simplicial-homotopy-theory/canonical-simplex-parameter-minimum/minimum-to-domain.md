# Natural transformation from minimum to source coordinates

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`, the natural transformation
`(minimumCoordinates τ ρ).toFunctor ⟶ (domainCoordinates τ ρ).toFunctor` induced by the
pointwise inequality. Its component at `(x, k)` is the unique preorder arrow from `(τ(x), min
(ρ(x), k))` to `(τ(x), ρ(x))`.
