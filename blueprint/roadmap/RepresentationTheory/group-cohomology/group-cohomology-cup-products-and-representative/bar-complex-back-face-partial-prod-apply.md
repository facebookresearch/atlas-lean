# Back face in bar coordinates

Let `G` be a group, `k` a commutative ring, `p,q : ℕ`, and `f : Fin (p + q) → G`. Apply the
degree-`q` back face to `MonoidAlgebra.single (Fin.partialProd f) 1`, then transport to the
bar complex. The result is the bar basis vector with final tuple `i ↦ f (Fin.natAdd p i)` and
group-ring coefficient `single (Fin.partialProd f p) 1`, where the latter group element is the
ordered product of the initial `p` entries.
