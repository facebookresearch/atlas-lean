# Initial simplex of the upper-face pass

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and `h : Fin (n + 3) → (underlying G) _⦋n + 1⦌`,
`upperPass G i h (Fin.last (n + 2)) = lowerPass G h i`.
The descending pass begins with the lower-pass simplex at the missing-face index.
