# Cochain homotopy for a change of right transversal

Let `R` be a ring, `G` a group, `M` an abelian `R`-module, and `ρ : Representation R G M`, in
independent universes. For `H ≤ G` finite index, right transversals `T,U`, and `n : ℕ`, put
`K_j=schreierPrism ρ T U j`. For every `f ∈ C^{n+1}(H,M)`, `d_G(K_n f) + K_{n+1}(d_H f) =
Tr_U^{n+1} f - Tr_T^{n+1} f` as cochains on `G`. Here `Tr_T^m f(tuple)=∑ t∈T,
ρ(t⁻¹)f(T.schreierFactorTuple t tuple)`, and the degree-`m` differential is `d
c(tuple)=ρ(tuple 0)c(Fin.tail tuple)+∑ j : Fin (m+1), (-1)^(j+1) • c(Fin.contractNth j (· * ·)
tuple)`, using the restricted action on `H`.
