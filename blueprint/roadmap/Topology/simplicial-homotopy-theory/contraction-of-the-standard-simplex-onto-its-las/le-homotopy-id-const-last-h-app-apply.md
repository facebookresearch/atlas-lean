# The last-vertex contraction increases simplex coordinates

For `n : ℕ`, `a : SimplexCategoryᵒᵖ`, simplices `α ∈ (Δ[n] : SSet.{u}).obj a` and `t ∈ (Δ[1] : SSet.{u}).obj a`, and every `i : Fin (a.unop.len + 1)`,
`asOrderHom α i ≤ asOrderHom ((homotopyIdConstLast n).h.app a ⟨α, t⟩) i`.
The contraction fixes a coordinate when the corresponding interval coordinate is zero and otherwise sends it to the last vertex.
