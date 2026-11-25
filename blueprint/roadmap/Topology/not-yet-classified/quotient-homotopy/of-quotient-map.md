# Of Quotient Map

Descend a continuously parameterized homotopy through a quotient map.

Given a quotient map `q : X ⟶ Y` and a continuous homotopy `H : I × X → Z`
that at each `t` factors through `q`, produce the descended homotopy
`I × Y → Z` between `f` and `g`. The hypothesis `hFactors` supplies the
factorisation at each fixed `t`; continuity of the descended homotopy in both
variables follows from `IsQuotientMap.continuous_lift_prod_right` because
`unitInterval` is locally compact.
