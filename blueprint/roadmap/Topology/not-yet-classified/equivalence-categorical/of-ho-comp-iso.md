# A map with a homotopy inverse up to isomorphism in the homotopy categories of functor objects is a categorical equivalence

**A map with a homotopy inverse up to isomorphism in the homotopy
categories of functor objects is a categorical equivalence.** If
`g : Y ⟶ X` is such that the vertices classified by `f ≫ g` and `𝟙 X` are
isomorphic in `SSet.hoFunctor.obj ((ihom X).obj X)` and the vertices
classified by `g ≫ f` and `𝟙 Y` are isomorphic in
`SSet.hoFunctor.obj ((ihom Y).obj Y)`, then `f` is a Joyal categorical
equivalence: for every quasicategory `C`, whiskering the given
isomorphisms through `SSet.hoComp` exhibits precomposition with `g` as a
quasi-inverse of precomposition with `f` on `h Fun(-, C)`. This is the
homotopy-equivalence condition of Stevenson, Definition 2.1, read in
ordinary homotopy categories; see the module header.
