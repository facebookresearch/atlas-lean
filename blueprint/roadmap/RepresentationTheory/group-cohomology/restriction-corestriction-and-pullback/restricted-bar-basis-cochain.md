# Ambient bar basis on subgroup tuples

Let `G` be a group, `k` a commutative ring, `H ≤ G`, and `n : ℕ`. The function
`restrictedBarBasisCochain n : (Fin n → H) → (Rep.barComplex k G).X n` sends `q` to `barBasis
n (fun i => (q i : G))`, using the subgroup inclusion in every tuple coordinate.
