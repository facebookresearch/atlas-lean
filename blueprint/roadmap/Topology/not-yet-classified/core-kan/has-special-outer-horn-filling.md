# Has Special Outer Horn Filling

Joyal's special outer horn filling property for a simplicial
set `X`, in dimensions at least `2`: every left outer horn
`Λ[n + 2, 0] ⟶ X` whose `(0, 1)`-edge is an equivalence extends to
`Δ[n + 2]`, and every right outer horn `Λ[n + 2, n + 2] ⟶ X` whose
last edge is an equivalence extends to `Δ[n + 2]`. For `n = 0` this
is proved for every quasicategory in this file
(`exists_fill_horn_two_zero_of_isEquivalence`,
`exists_fill_horn_two_last_of_isEquivalence`); for `n ≥ 1` it is
proved in
`MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral`
(`SSet.hasSpecialOuterHornFilling_of_quasicategory`).
