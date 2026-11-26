# Bar basis with unit group-ring coefficient

Let `G` be a group, `k` a commutative ring, `n : ℕ`, and `g : Fin n → G`. The element
`barBasis n g` of `(Rep.barComplex k G).X n` is `Finsupp.single g (MonoidAlgebra.single 1 1)`,
the bar basis vector at `g` with unit group-ring coefficient.
