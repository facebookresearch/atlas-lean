# Relative Chain Complex Functor

The coefficient-natural unnormalized relative chain complex functor.
For `R : C`, this sends a simplicial pair `X = (A ↪ X₀)` to the cokernel of
`C_*(A;R) ⟶ C_*(X₀;R)`. It is defined as the composite

`SSet.chainComplexFunctor C`
`⋙ Functor.mapArrowFunctor`
`⋙ (whiskeringLeft SSetPair.forget)`
`⋙ (whiskeringRight Limits.coker)`,

so naturality and functor laws are inherited from categorical composition.
