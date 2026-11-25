# Alternating

Generic degreewise Alexander–Whitney component on alternating-face complexes.

For `n : ℕ` this is a morphism from degree `n` of
`(alternatingFaceMapComplex C).obj (X ⊗ Y)` to degree `n` of
`HomologicalComplex.tensorObj` of the alternating-face complexes of `X` and `Y`,
given by `∑ p : Fin (n + 1)`,
`let q := n - (p : ℕ)`, `have h : (p : ℕ) + q = n := by omega`,
`(frontFace X h ⊗ₘ backFace Y h) ≫ HomologicalComplex.ιTensorObj _ _ _ _ _ h`.

`AlexanderWhitney.ChainMap` packages these components as a natural chain map.
