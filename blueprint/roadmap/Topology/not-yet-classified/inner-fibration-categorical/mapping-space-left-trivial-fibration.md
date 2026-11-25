# Mapping Space Left Trivial Fibration

The conclusion of Stevenson's Step 1 for a map `p`: every
induced map on naive (left, join-slice) mapping spaces
`Homᴸ_X(a, b) → Homᴸ_S(a ≫ p, b ≫ p)` is a trivial Kan
fibration. For an inner fibration `p` between pre-fibrant
simplicial sets which is a categorical equivalence, Stevenson
deduces this from Proposition 3.5 and Remark 3.7 (weak
equivalences between the Kan complexes of Remark 3.3) plus the
Kan-fibration property of fibers of the left fibration
`SSet.sliceUnderComparison`; none of those inputs is landed, so
in this file the predicate is only named and given its formal
sanity properties. Compare `SSet.dwyerKanFullyFaithfulLeft`
(Descent.lean), which asks for a realization weak equivalence
of the same maps: the present predicate is the fibration
strengthening that Step 3 actually consumes.
