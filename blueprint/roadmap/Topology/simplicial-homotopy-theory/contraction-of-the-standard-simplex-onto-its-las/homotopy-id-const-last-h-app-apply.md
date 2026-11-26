# Coordinates of the last-vertex contraction

Let `n : ℕ`, `a : SimplexCategoryᵒᵖ`, `α ∈ (Δ[n] : SSet.{u}).obj a`, and `t ∈ (Δ[1] : SSet.{u}).obj a`. For every `i : Fin (a.unop.len + 1)`, the `i`-th coordinate of the contraction cylinder is
`asOrderHom ((homotopyIdConstLast n).h.app a ⟨α, t⟩) i = if asOrderHom t i = 0 then asOrderHom α i else Fin.last n`.
Thus the formula applies to every interval simplex `t`.
