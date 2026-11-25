# Iteration Functor Map Succ App Arrow Iso

For any `f : Arrow C` and `j : κ.ord.ToType`, the morphism
`((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f` identifies
to a morphism given by `SmallObject.ε I.homFamily`.
