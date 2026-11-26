# Prism tuple of Schreier factors

Let `G` be a group, `H ≤ G`, `T,U` right transversals, `t ∈ T`, and `tuple : Fin n → G`. For
`i : Fin (n + 1)`, `T.schreierPrismTuple U t tuple i` inserts the change factor
`c_i=T.schreierChangeScan U t tuple i` after the first `i` entries of the `T` factor tuple,
then uses the remaining entries of the `U` tuple starting at `T.changeRep U t`. Its ordered
entries are `(a₀,…,a_{i-1},c_i,b_i,…,b_{n-1})`.
