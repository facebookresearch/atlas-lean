# Homogeneous simplex as a bar basis vector

For a group `G` and a commutative ring `k`, the degree-`n` standard-to-bar comparison sends
`MonoidAlgebra.single u r`, for `u : Fin (n + 1) → G`, to the bar basis vector with tuple `i ↦
(u i)⁻¹ * u (i + 1)` and group-ring coefficient `MonoidAlgebra.single (u 0) r`.
