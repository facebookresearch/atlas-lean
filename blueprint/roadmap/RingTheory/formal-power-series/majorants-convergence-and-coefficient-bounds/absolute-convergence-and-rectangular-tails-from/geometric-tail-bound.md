# Geometric tail bound

For a geometric majorant `m` on `Fin d` with bound `M` and radii `R_i`, a
box `b : Fin d → ℚ≥0` and truncation orders `N : Fin d → ℕ`, the tail bound
is the rational number `M · (∑ i, q_i ^ N_i) · ∏ i, (1 - q_i)⁻¹`, where `q_i
= b_i / R_i`. The number is defined for every box. When `a` is majorized by `m`, every
`b_i < R_i` and `|x_i| ≤ b_i`, it bounds the terms omitted by the rectangular
window `α i < N i`, by a union bound over the axes along which an omitted
exponent leaves the window; otherwise it can be negative (for one variable
with `M = R = N = 1` and `b = 2` it is `-2`).
