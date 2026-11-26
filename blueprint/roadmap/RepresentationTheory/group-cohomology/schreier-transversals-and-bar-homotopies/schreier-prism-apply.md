# Value of the signed Schreier prism

Let `R` be a ring, `G` a group, `M` an abelian `R`-module, and `ρ : Representation R G M`,
with independent scalar, group, and coefficient universes. For `H ≤ G` finite index, right
transversals `T,U`, `n : ℕ`, `f : (Fin (n+1) → H) → M`, and `tuple : Fin n → G`,
`schreierPrism ρ T U n f tuple = ∑ t∈T, ρ(t⁻¹)(∑ i : Fin (n+1), (-1)^i •
f(T.schreierPrismTuple U t tuple i))`.
