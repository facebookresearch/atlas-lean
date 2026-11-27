# Curry' comp pre app

Currying a map and then precomposing the internal hom corresponds to
precomposing the map itself: `curry' g ≫ (pre f).app C = curry' (f ≫ g)`.
The proof uncurries both sides and uses
`MonoidalClosed.uncurry_pre_app` together with naturality of the right
unitor.
