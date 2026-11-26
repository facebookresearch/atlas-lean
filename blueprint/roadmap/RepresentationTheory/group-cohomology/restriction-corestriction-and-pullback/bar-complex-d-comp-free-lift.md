# Bar differential and inhomogeneous cochain differential

Let `G` be a group, `k` a commutative ring, `A : Rep k G`, `n : ℕ`, and `f : (Fin n → G) → A`.
For the bar complex `B`, `B.d (n + 1) n ≫ Rep.freeLift k G A f = Rep.freeLift k G A
((inhomogeneousCochains.d A n).hom f)`. Thus the inhomogeneous differential corresponds to
precomposition by the bar differential.
