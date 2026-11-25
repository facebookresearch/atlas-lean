# `joinInr` on standard simplices is `inr'`

The right
endpoint inclusion of a join of standard simplices, transported
along `joinStdSimplexIso`, is the standard-simplex map of
`AugmentedSimplexCategory.inr'`. Mirror of
`SSet.joinInl_comp_joinStdSimplexIso_hom`; expanding `joinInr`
(left unitor, then whiskering `initial.to` on the left) and
`joinStdSimplexIso` in `DayCat` reduces it to
`SSet.Join.joinInrDay_eq` and naturality of `dropYonedaIso`.
