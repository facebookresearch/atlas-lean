# Associativity of bar-cochain cup pairings

Let `G` be a group, `k` a commutative ring, `A,B,D` representations, and `p,q,r : ℕ`. Put
`Y(A)_n = Hom_G((Rep.barComplex k G).X n,A)` and write `P` for the bar cup pairings. Then
`(P_{A,B}(p,q) ⊗ 𝟙) ≫ P_{A⊗B,D}(p+q,r) ≫ α_* ≫ e = α_{Y(A)_p,Y(B)_q,Y(D)_r} ≫ (𝟙 ⊗
P_{B,D}(q,r)) ≫ P_{A,B⊗D}(p,q+r)`. Here `α_*` postcomposes bar cochains by `(α_ A B D).hom`,
and `e` identifies `(p + q) + r` with `p + (q + r)`.
