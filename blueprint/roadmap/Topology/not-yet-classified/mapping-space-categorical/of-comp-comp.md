# Two-out-of-six for full faithfulness on mapping spaces

**Two-out-of-six for full faithfulness on mapping spaces** (the
formal conclusion of Stevenson's proof of Lemma 2.17): if
`f ≫ g` and `g ≫ f` are fully faithful in the sense of
`SSet.dwyerKanFullyFaithful`, then `f` is. At vertices `a b` this
applies `SSet.realizationWeakEquivalences.left_of_comp_comp`
to the chain of
mapping-space maps at `a`, `a ≫ f` and `(a ≫ f) ≫ g`, whose two
consecutive composites are the mapping-space maps of `f ≫ g` and
`g ≫ f` by `SSet.mappingSpaceRight.map_comp`.
