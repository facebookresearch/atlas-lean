# D squared

The alternating face differential squares to zero.

This proof follows Mathlib's native simplicial alternating-face proof: expand
the composite as a double sum and pair the two regions by `(i, j) ↦ (j, i+1)`.
Only the semisimplicial face identity is used.
