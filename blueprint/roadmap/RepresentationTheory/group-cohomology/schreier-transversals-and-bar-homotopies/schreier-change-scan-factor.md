# Commuting squares of Schreier and change factors

Let `G` be a group, `H ≤ G`, `T,U` right transversals, `t ∈ T`, `tuple : Fin n → G`, and `i :
Fin n`. Put `a_i=T.schreierFactorTuple t tuple i`, `b_i=U.schreierFactorTuple (T.changeRep U
t) tuple i`, and `c_j=T.schreierChangeScan U t tuple j`. These elements of `H` satisfy `a_i *
c_{i+1} = c_i * b_i`.
