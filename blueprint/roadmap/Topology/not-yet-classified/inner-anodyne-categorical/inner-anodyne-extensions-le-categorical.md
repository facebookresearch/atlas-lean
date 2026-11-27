# Inner anodyne extensions are categorical equivalences

Every inner
anodyne extension is a Joyal weak categorical equivalence: for every
quasicategory `C`, precomposition with an inner anodyne extension induces
an equivalence `h Fun(Y, C) ⟶ h Fun(X, C)` of homotopy categories, because
that precomposition map is a trivial Kan fibration
(`SSet.rlp_I_pre_app_of_innerAnodyneExtensions`) and trivial Kan
fibrations induce equivalences of homotopy categories
(`SSet.hoFunctor_map_isEquivalence_of_rlp_I`).
