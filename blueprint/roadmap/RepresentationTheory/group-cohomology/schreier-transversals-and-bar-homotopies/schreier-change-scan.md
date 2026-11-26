# Change factors along a Schreier scan

Let `G` be a group, `H ≤ G`, `T,U` right transversals, `t ∈ T`, and `tuple : Fin n → G`. The
change-factor scan is `i ↦ T.changeFactor U (T.schreierRepScan t tuple i)` in `H`, for `i :
Fin (n + 1)`. Its value `c_i` compares the representatives at the prefix product by `r_i^T =
c_i r_i^U`.
