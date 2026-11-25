# Dwyer Kan Fully Faithful Left

The fully-faithful half of Stevenson Definition 2.16(ii) and
Remark 3.7, stated with the *left* mapping spaces
`Homᴸ_X(x, y) = SSet.mappingSpaceLeft X x y` of
`JoinSlice.lean`, as in the paper (the landed
`SSet.dwyerKanFullyFaithful` uses right mapping spaces; see
the additional comparison obligation): for all vertex maps `a b : Δ[0] ⟶ X`, the
induced map `mappingSpaceLeft X a b ⟶ mappingSpaceLeft Y (a ≫ f)
(b ≫ f)` is a realization weak equivalence. Like the landed
right-handed predicate, this uses
`SSet.realizationWeakEquivalences`, which is defined on arbitrary
simplicial sets and imposes no Kan hypothesis on the mapping
spaces; when the mapping spaces are Kan complexes it agrees with
`SSet.KanComplex.W` by
`SSet.KanComplex.W_iff_realizationWeakEquivalence` (see
`SSet.dwyerKanFullyFaithfulLeft.of_kanComplexW` and
`SSet.dwyerKanFullyFaithfulLeft.kanComplexW` below). For
pre-fibrant `X, Y`, Kan-ness of the left mapping spaces is the
unproved Remark 3.3 (the additional comparison obligation).
