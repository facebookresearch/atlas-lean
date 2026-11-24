# Of Hom δ tensor Hom id

Tensoring a face map with the identity on `⦋0⦌` in the
augmented simplex category is the same face map one dimension
up. Proof by `tensorObj_hom_ext`: both `inl` and `inr`
precompositions agree, by `inl_comp_tensorHom`,
`inr_comp_tensorHom`, `SSet.inl'_eq_δ_last`,
`SSet.inr'_comp_δ_castSucc` and `SSet.δ_last_comp_δ_castSucc`
(the augmented equalities are the simplex-category equalities,
since homs between `of`-objects and their composition are
definitionally those of `SimplexCategory`).
