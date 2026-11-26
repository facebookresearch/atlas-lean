# Bar differential as a basis-valued cochain

Let `G` be a group, `k` a commutative ring, and `n : ℕ`. Put `B_n=(Rep.barComplex k G).X n`.
The cochain `barDifferentialCochain n : (Fin (n + 1) → G) → B_n` is `(inhomogeneousCochains.d
B_n n).hom (barBasisCochain n)`, the inhomogeneous differential of the cochain sending each
degree-`n` tuple to its unit-coefficient bar basis vector.
