# Chain Homotopy Equiv Of Simplicial Homotopy Equiv

The chain homotopy equivalence induced by a simplicial homotopy equivalence:
two maps `f : X ⟶ Y`, `g : Y ⟶ X` with simplicial homotopies `f ≫ g ≃ 𝟙` and
`g ≫ f ≃ 𝟙` give a chain `HomotopyEquiv` whose forward and inverse are
exactly `SSet.chainComplexMap f R` and `SSet.chainComplexMap g R`. Homotopies are
obtained via `SimplicialObject.Homotopy.sSetChainComplexMap` transported along
`Functor.map_comp` and `Functor.map_id`.
