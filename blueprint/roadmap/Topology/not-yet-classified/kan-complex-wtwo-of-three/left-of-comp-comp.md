# Two-out-of-six for `SSet.KanComplex.W`, left map

If
`a ≫ b` and `b ≫ c` are weak equivalences between Kan complexes
then so is `a`. This does not follow from abstract two-out-of-three
for `W` (`SSet.KanComplex.W.hasTwoOutOfThreeProperty`); it is
proved from the defining invariants: equivalences of categories
satisfy two-out-of-six (`isEquivalence_of_comp_comp_middle` plus
cancellation), and for the based homotopy-group maps at a vertex
`x` of `A`, the two composite bijections force the middle map at
`a.app _ x` to be bijective (injective from the second composite,
surjective from the first), hence the first map is bijective. The
analogous statements for the middle and right maps at *arbitrary*
basepoints would additionally need basepoint transport along the
fundamental groupoid (as in `SSet.KanComplex.W.of_precomp`) and
are not needed here.
