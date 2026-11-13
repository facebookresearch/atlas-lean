# Berge maximum continuous value

Berge's maximum theorem, value part. Let `φ : X → Set Y` be a correspondence with nonempty
compact values that is both upper and lower hemicontinuous, and let the objective
`f : X → Y → ℝ` be jointly continuous. Then the value function
`x ↦ sSup (f x '' φ x)` is continuous. (With `φ` constant this is Mathlib's
`IsCompact.continuous_sSup`.)
