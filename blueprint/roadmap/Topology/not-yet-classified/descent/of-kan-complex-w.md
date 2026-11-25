# Of kan Complex W

Bridge from `SSet.KanComplex.W` to full faithfulness on left
mapping spaces: if every induced map on left mapping spaces is a
`SSet.KanComplex.W` weak equivalence, then `f` is fully faithful
on left mapping spaces. This is
`SSet.KanComplex.W_iff_realizationWeakEquivalence` applied
pointwise, with the `SSet.KanComplex` instances extracted from
each `hW a b` by `SSet.KanComplex.W.kanComplex_source` and
`SSet.KanComplex.W.kanComplex_target`; no separate Kan
hypotheses are needed.
