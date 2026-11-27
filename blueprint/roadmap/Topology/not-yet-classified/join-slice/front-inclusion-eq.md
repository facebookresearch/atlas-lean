# `frontInclusion` is the last face map

The transported
left endpoint inclusion `SSet.frontInclusion n : Δ[n] ⟶ Δ[n + 1]`
is `stdSimplex.δ (Fin.last (n + 1))`. Via
`SSet.joinInl_comp_joinStdSimplexIso_hom` and `SSet.inl'_eq_δ_last`
(from `JoinProperties.lean`).
