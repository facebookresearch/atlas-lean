# Degree-zero homotopy for a change of right transversal

Let `R` be a ring, `G` a group, `M` an abelian `R`-module, and `ρ : Representation R G M`, in
independent universes. For `H ≤ G` finite index, right transversals `T,U`, and a zero-cochain
`f : (Fin 0 → H) → M`, put `m=f(empty)`. The identity is `schreierPrism ρ T U 0 (fun y => ρ(y
0)m - m)(empty) = ∑ u∈U, ρ(u⁻¹)m - ∑ t∈T, ρ(t⁻¹)m`. Thus `K₀ d_H f = Tr_U^0 f - Tr_T^0 f` with
the same signed prism and inverse-representative weights.
