# A categorical equivalence induces an equivalence of ordinary homotopy categories

**A categorical equivalence induces an equivalence of ordinary
homotopy categories** using the ordinary nerve comparison functor. No quasicategory hypothesis on
source or target is needed: test against the nerves
`nerve X.HomotopyCategory` and `nerve Y.HomotopyCategory`.
Essential surjectivity at the vertex of `CategoryTheory.nerveAdjunction.unit.app X` gives
`g : Y ⟶ nerve X.HomotopyCategory`; the object formula
`SSet.hoFunNerveComparison_obj_mk_ihomVertexEquiv` turns the
resulting isomorphism into `mapHomotopyCategory f ⋙ descNerve g ≅ 𝟭`,
and postcomposing with `nerveMap (mapHomotopyCategory f)`,
transporting along `CategoryTheory.nerveAdjunction.unit.naturality`, and reflecting
along the equivalence at `nerve Y.HomotopyCategory`
(`Functor.preimageIso`) gives the other triangle
`descNerve g ⋙ mapHomotopyCategory f ≅ 𝟭`.
