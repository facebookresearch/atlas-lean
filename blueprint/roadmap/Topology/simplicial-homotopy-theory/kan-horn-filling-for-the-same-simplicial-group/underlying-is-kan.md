# Every simplicial group has a Kan underlying simplicial set

For any `G : SimplicialObject GrpCat.{u}`, the underlying simplicial set `underlying G` is a
Kan complex. Equivalently, for every `n : ℕ` and `i : Fin (n + 2)`, every simplicial map from
the horn `Λ_i[n + 1]` to `underlying G` extends to `Δ[n + 1]`. The groups of `G` need not be
commutative.
