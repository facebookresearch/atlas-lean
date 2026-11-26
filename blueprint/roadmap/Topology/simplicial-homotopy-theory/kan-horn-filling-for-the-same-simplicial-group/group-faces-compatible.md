# Horn compatibility gives degree-group face equations

Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, and `i : Fin (n + 3)`. Suppose the maps `f j
hj : Δ[n + 1] ⟶ underlying G`, for `j ≠ i`, form a compatible horn family
(`SSet.horn.IsCompatible f`). Then `FaceCompatible G i (groupFaces G i f)` holds: for `k : Fin
(n + 2)` and `j : Fin (n + 3)` with `Fin.castSucc k < j` and both indices different from `i`,
the `k`-th face of the value at `j` equals the `(j - 1)`-st face of the value at `Fin.castSucc
k`.
