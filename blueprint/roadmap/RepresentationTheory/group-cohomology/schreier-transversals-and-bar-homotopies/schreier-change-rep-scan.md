# Matching representatives along a prefix scan

Let `G` be a group, `H ≤ G`, `T,U` right transversals, `t ∈ T`, `tuple : Fin n → G`, and `i :
Fin (n + 1)`. Then `T.changeRep U (T.schreierRepScan t tuple i) = U.schreierRepScan
(T.changeRep U t) tuple i`. Thus changing the initial representative and scanning the ordered
prefix products agrees with changing each scanned representative.
