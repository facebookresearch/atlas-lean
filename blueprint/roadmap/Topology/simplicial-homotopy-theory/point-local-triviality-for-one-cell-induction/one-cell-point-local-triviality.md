# Point-local triviality with a fixed fiber

For `p : E ⟶ X₄`, `F : TopCat.{u}`, and `pt : X₄`, point-local triviality is the existence of
a subset `U ⊆ X₄` such that `IsOpen U`, `pt ∈ U`, and `TrivialBundleWithFiberOver F p
(AlgebraicTopology.subspaceIncl U)` is nonempty. Such a presentation is a pullback of `p` over
`U` whose total space, with its projection, is a product of `U` and `F`.
