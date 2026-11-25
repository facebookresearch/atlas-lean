# Of kan Complex W

Bridge from `SSet.KanComplex.W` to full faithfulness: if all
source right mapping spaces and all target right mapping spaces at
`f`-image vertices are Kan complexes, and every induced map on
right mapping spaces is a `SSet.KanComplex.W` weak equivalence,
then `f` is fully faithful on mapping spaces. This is
`SSet.KanComplex.W_iff_realizationWeakEquivalence` applied
pointwise, with the `SSet.KanComplex` instances supplied from
`hKanX` and `hKanY`.
