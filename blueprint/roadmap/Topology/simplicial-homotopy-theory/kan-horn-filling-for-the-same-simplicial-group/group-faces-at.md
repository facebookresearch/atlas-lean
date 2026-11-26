# Yoneda value of a prescribed horn face

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and a family of maps `f j hj : Δ[n + 1] ⟶ underlying G` indexed by `j ≠ i`,
`groupFaces G i f j = yonedaEquiv (f j hj)`
whenever `hj : j ≠ i`. Thus every prescribed face retains its Yoneda value.
