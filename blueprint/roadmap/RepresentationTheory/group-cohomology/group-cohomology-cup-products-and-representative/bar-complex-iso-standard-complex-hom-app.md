# Bar basis vector as a homogeneous simplex

For a group `G` and a commutative ring `k`, the degree-`n` bar-to-standard comparison sends
`single f (MonoidAlgebra.single g r)` to `MonoidAlgebra.single (g • Fin.partialProd f) r`, for
`f : Fin n → G`, `g : G`, and `r : k`. The homogeneous tuple is `(g, g f₀, g f₀ f₁, …)`, with
products taken in the displayed order.
