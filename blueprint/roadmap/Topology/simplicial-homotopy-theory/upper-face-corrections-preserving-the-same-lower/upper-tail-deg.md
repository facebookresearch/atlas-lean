# Degeneracy index for a later-face comparison

For `n : ℕ`, `j : Fin (n + 2)`, `k : Fin (n + 3)`, and `hjk : j.succ < k`, the index
`upperTailDeg hjk : Fin (n + 1)` is `j` with its bound tightened. The inequality implies `j <
n + 1`, so its successor is an admissible face index for a degree-`n + 1` simplex.
