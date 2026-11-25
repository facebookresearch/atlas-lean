# Dwyer Kan Fully Faithful

The fully-faithful half of Stevenson Definition 2.16(ii), stated
with the join-slice *right* mapping spaces of `JoinSlice.lean`
(Stevenson uses left mapping spaces; see the references above): for all vertex
maps `a b : Δ[0] ⟶ X`, the induced map
`mappingSpaceRight X a b ⟶ mappingSpaceRight Y (a ≫ f) (b ≫ f)`
given by postcomposition (`SSet.mappingSpaceRight.map`) is a
realization weak equivalence (`SSet.realizationWeakEquivalences`,
the weak equivalences of the Quillen model structure on simplicial
sets). For element vertices `x : X _⦋0⦌` the vertex map is
`SSet.const x` and its image is the vertex map of the image vertex,
since `const x ≫ f = const (f.app _ x)` by `SSet.const_comp`; see
`SSet.dwyerKanFullyFaithful.vertex`. Note
`SSet.realizationWeakEquivalences` is defined on arbitrary
simplicial sets and imposes no Kan hypothesis on the mapping
spaces; when the mapping spaces are Kan complexes it agrees with
`SSet.KanComplex.W` by
`SSet.KanComplex.W_iff_realizationWeakEquivalence` (see
`SSet.dwyerKanFullyFaithful.of_kanComplexW` and
`SSet.dwyerKanFullyFaithful.kanComplexW`).
