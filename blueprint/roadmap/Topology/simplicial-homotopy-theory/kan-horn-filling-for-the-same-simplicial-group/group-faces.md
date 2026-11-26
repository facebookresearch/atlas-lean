# Degree-group elements associated to horn faces

Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, and `i : Fin (n + 3)`. Given maps `f j hj :
Δ[n + 1] ⟶ underlying G` for every `j ≠ i`, the family `groupFaces G i f : Fin (n + 3) →
(underlying G) _⦋n + 1⦌` assigns `yonedaEquiv (f j hj)` to a nonmissing face `j`, and assigns
the group identity to the missing index `i`.
