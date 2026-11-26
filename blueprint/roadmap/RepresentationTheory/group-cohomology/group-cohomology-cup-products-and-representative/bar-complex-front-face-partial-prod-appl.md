# Front face in bar coordinates

Let `G` be a group, `k` a commutative ring, `p,q : ℕ`, and `f : Fin (p + q) → G`. Apply the
degree-`p` front face to `MonoidAlgebra.single (Fin.partialProd f) 1`, then transport from the
standard to the bar complex. The result is `single (fun i => f (Fin.castAdd q i))
(MonoidAlgebra.single 1 1)`: the initial `p` entries with unit group-ring coefficient.
