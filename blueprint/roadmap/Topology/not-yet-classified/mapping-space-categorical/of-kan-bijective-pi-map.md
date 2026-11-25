# Whitehead criterion for full faithfulness

If all right
mapping spaces of `X` and all the target right mapping spaces are
Kan complexes, and for every pair of vertices the induced map
`SSet.mappingSpaceRight.map X a b f` induces an equivalence of
fundamental groupoids and bijections on all based homotopy groups,
then `f` is fully faithful on mapping spaces. This is
`SSet.KanComplex.W.mk` applied pointwise and transported along
`SSet.dwyerKanFullyFaithful.of_kanComplexW`; it isolates exactly the
hypotheses (Kan-ness — discharged for quasicategories by
`SSet.kanComplex_mappingSpaceRight` downstream, formerly
the additional comparison obligation — and the higher-homotopy input,
the additional comparison obligation) that remain between a categorical
equivalence and `SSet.dwyerKanFullyFaithful`.
