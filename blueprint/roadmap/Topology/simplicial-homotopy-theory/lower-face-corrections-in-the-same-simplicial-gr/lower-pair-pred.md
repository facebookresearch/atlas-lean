# Predecessor index in lower-face compatibility

For `n : ℕ`, `k, j : Fin (n + 2)`, and `hkj : k < j`, the index `lowerPairPred hkj : Fin (n +
2)` is `(Fin.castSucc j).pred _`, whose value is `j - 1`. The inequality guarantees that this
predecessor is defined; it is the second face index in the relation `δ k ∘ δ j = δ (j - 1) ∘ δ
k`.
