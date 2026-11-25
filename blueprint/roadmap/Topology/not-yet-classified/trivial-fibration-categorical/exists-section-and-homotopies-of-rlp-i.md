# Section and coherent homotopies for a trivial Kan fibration

A
trivial Kan fibration `p : X ⟶ Y` admits a strict section `s : Y ⟶ X`
(`SSet.exists_section_of_rlp_I`) together with simplicial homotopies over
`p`, in both directions, between `𝟙 X` and `p ≫ s`: the homotopies `H`
satisfy `H.h ≫ p = CartesianMonoidalCategory.fst X Δ[1] ≫ p`, i.e. they
lie over the constant homotopy of `p` in `Y`. The homotopies are the
coherent cylinder homotopies of `SSet.exists_homotopy_over_of_rlp_I`,
applied to `(p ≫ s) ≫ p = p`.
