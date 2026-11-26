# Faces preserved and filled by an upper-pass stage

Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and `h : Fin (n + 3) →
(underlying G) _⦋n + 1⦌` satisfy `FaceCompatible G i h`, the pairwise simplicial face
equations away from `i`. For a stage `r : Fin (n + 3)` with `i ≤ r`, the `(n + 2)`-simplex
`upperPass G i h r` has face `h k` at every index `k < i` and every index `r < k`. Thus the
pass preserves all prescribed lower faces and fills the faces strictly above its stage.
