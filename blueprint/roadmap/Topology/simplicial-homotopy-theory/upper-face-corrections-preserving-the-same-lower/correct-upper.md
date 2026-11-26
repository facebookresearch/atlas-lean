# Correction of an upper face by a degeneracy

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 1)`, `x ∈ (underlying G) _⦋n + 1⦌`, and prescribed face `h ∈ (underlying G) _⦋n⦌`,
`correctUpper G j x h = x * (underlying G).σ j (upperError G j x h)`.
The error for face `j + 1` is lifted by degeneracy `j` and multiplied on the right of `x`.
