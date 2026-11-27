# Rlp I pre app of inner Anodyne Extensions

Precomposition with an inner anodyne extension `f` into a
quasicategory `C` is a trivial Kan fibration: the map
`(MonoidalClosed.pre f).app C` has the right lifting property against the
generating cofibrations `SSet.modelCategoryQuillen.I` (the boundary
inclusions). The lifting problem against `∂Δ[n].ι` transposes, under the
parametrized tensor–internal-hom adjunction, to the lifting problem of
the pushout-product of `f` with `∂Δ[n].ι` against the inner fibration
`C ⟶ ⊤_ SSet`, and that pushout-product is inner anodyne by
`SSet.innerAnodyneExtensions_pushoutObjObjι'`.
