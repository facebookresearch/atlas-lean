# Natural transformation from minimum to external coordinates

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`, the natural transformation
`(minimumCoordinates τ ρ).toFunctor ⟶ (pullbackCoordinates τ).toFunctor` induced by the
pointwise inequality. At `(x, k)`, its component is the unique preorder arrow from `(τ(x), min
(ρ(x), k))` to `(τ(x), k)`.
