# Signed Schreier prism on cochains

Let `R : Type r` be a ring, `G : Type g` a group, `M : Type v` an abelian group with an
`R`-module structure, and `ρ : Representation R G M`. For `H ≤ G` finite index, right
transversals `T,U`, and `n : ℕ`, `schreierPrism ρ T U n` is the linear map `C^{n+1}(H,M) →ₗ[R]
C^n(G,M)` with value `K_n f(tuple) = ∑ t∈T, ρ(t⁻¹)(∑ i : Fin (n+1), (-1)^i •
f(T.schreierPrismTuple U t tuple i))`. The universes `r,g,v` are independent.
