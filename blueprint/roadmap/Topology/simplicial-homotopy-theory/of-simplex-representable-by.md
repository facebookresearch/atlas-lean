# Representability of a simplex-generated subcomplex

Let `X : SSet.{u}`, `n : ℕ`, and `x : X _⦋n⦌`. If the Yoneda map `yonedaEquiv.symm x : Δ[n] ⟶
X` is a monomorphism, then `Subcomplex.ofSimplex x` is represented by `⦋n⦌`. The
representation identifies its simplices naturally with ordinal maps into `⦋n⦌`, using the
isomorphism `Subcomplex.toOfSimplex x : Δ[n] ⟶ Subcomplex.ofSimplex x`.
