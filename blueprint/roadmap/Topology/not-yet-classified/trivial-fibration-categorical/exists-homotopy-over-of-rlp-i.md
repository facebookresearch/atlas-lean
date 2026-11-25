# Coherent cylinder homotopy over a trivial Kan fibration

If `p` is
a trivial Kan fibration and `a b : X ⟶ X` become equal after composition
with `p`, then `a` and `b` are simplicially homotopic by a homotopy lying
over the constant homotopy of `a ≫ p` in `Y`: there is
`H : SSet.Homotopy a b` with
`H.h ≫ p = CartesianMonoidalCategory.fst X Δ[1] ≫ (a ≫ p)`.

The proof is a single lift of `p` against the monomorphism
`X ◁ (boundary 1).ι : X ⊗ ∂Δ[1] ⟶ X ⊗ Δ[1]`
(`SSet.rlp_monomorphisms_of_rlp_I`), in the square whose top map
`X ⊗ ∂Δ[1] ⟶ X` is assembled from `a` and `b` on the two ends of the
cylinder and whose bottom map is `fst ≫ (a ≫ p)`; the square commutes
since `a ≫ p = b ≫ p`. This is the construction identified as the missing
input in the header of
`MathlibExt.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibration`.
