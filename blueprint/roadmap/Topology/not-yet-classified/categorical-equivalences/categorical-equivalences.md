# Categorical Equivalences

The morphism property of Joyal categorical equivalences between
simplicial sets. A map `f : X ⟶ Y` is tested by precomposition on the
simplicial functor objects into every quasicategory and passage to the
homotopy category: `f` is a categorical equivalence when the induced functor
`h Fun(Y, C) ⟶ h Fun(X, C)` is an equivalence of ordinary categories for
every quasicategory `C`.

This is the `hFun` formulation of weak categorical equivalence used in HTT
§2.2.5. Its equivalence with other formulations (bijectivity on isomorphism
classes, quasicategorical equivalences of functor objects) is a theorem
obligation elsewhere, not built into this definition.
