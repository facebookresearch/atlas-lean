# Assembly: a section plus a homotopy-category-level inverse gives a categorical equivalence

**Assembly: a section plus a homotopy-category-level inverse gives a
categorical equivalence.** If `p : X ⟶ Y` has a section `s` and, for every
quasicategory `C`, precomposition with `p ≫ s` is naturally isomorphic to
the identity functor on `h Fun(X, C)`, then `p` is a categorical
equivalence: the functors `h Fun(p, C)` and `h Fun(s, C)` are mutually
inverse equivalences, the composite at `Y` being strictly the identity by
`s ≫ p = 𝟙 Y`, `SSet.hoFunctor_pre_comp`, and `SSet.hoFunctor_pre_id`.
Combined with `SSet.exists_section_and_homotopies_of_rlp_I`, this reduces
the target of the supporting results to exhibiting the displayed natural isomorphism
from a simplicial homotopy; that step (the additional comparison obligation in the
module header) is formalized in `HoPreNatIso.lean` as
`SSet.hoPreNatIso_of_homotopy_over_of_rlp_I`, which there completes
`SSet.categoricalEquivalences.of_rlp_I`.
