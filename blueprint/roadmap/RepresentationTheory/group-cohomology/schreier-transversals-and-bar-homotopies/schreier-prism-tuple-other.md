# Other coordinates of the Schreier prism

Let `G` be a group, `H ≤ G`, `T,U` right transversals, `t ∈ T`, `tuple : Fin n → G`, `i : Fin
(n + 1)`, and `j : Fin n`. At the coordinate `i.succAbove j`, the prism tuple equals
`T.schreierFactorTuple t tuple j` if `j < i`, and `U.schreierFactorTuple (T.changeRep U t)
tuple j` otherwise. This gives all coordinates other than the inserted change factor.
