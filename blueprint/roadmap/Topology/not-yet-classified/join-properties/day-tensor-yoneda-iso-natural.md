# Naturality of `dayTensorYonedaIso`

Tensoring homs of
augmented representables and then applying
`dayTensorYonedaIso` equals applying `dayTensorYonedaIso` and
then the representable map of the tensored hom. The proof is
`DayFunctor.tensor_hom_ext` followed by the `η`-whisker lemmas
of `JoinProperties.lean`; on elements both sides send
`(up f, up g)` to `up ((f ≫ α) ⊗ₘ (g ≫ β)) = up ((f ⊗ₘ g) ≫
(α ⊗ₘ β))`.
