# Descent is injective

Two maps into a nerve with equal
descents agree. Direct `IsStrictSegal.hom_ext` proof: a `1`-simplex
of a nerve is `mk₁` of the morphism read off by
`CategoryTheory.nerve.homEquiv`, that morphism is the descent on the
corresponding generating morphism, and equality of the descents as
*arrows* is extracted without transports through `Functor.mapArrow`
(the same device upstream uses in `homToNerveMk`).
