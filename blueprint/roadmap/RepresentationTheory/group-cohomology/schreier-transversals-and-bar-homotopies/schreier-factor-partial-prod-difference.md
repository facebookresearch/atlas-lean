# Schreier factors from consecutive prefix products

Let `G` be a group, `H ≤ G`, `T` a right transversal, `t ∈ T`, `tuple : Fin n → G`, and `i :
Fin n`. Put `p_j=Fin.partialProd tuple j`. The factor tuple satisfies `(T.schreierFactor t
p_i)⁻¹ * T.schreierFactor t p_{i+1} = T.schreierFactorTuple t tuple i`. The inverse and
product have the displayed order in `H`.
