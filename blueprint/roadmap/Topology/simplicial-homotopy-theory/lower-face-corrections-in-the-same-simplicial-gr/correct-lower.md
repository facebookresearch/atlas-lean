# Correction of a lower face by a degeneracy

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 1)`, `x ∈ (underlying G) _⦋n + 1⦌`, and prescribed face `h ∈ (underlying G) _⦋n⦌`,
`correctLower G j x h = x * (underlying G).σ j (lowerError G j x h)`.
This is an `(n + 1)`-simplex obtained by multiplying `x` on the right by the degeneracy of its face error.
