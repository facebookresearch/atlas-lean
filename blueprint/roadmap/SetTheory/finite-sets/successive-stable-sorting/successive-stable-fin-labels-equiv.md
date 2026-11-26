# Finite labels for successive stable sorting

For `n,a,b : ℕ`, this is the equivalence `(Fin n → Fin a) × (Fin n → Fin b) ≃ (Fin n →
Fin(b*a))`. It sends `(f,g)` to the labeling whose value at input index `i` is
`finProdFinEquiv(g((Tuple.sort f)⁻¹ i), f i)`, with natural-number value `a*g((Tuple.sort f)⁻¹
i).val + (f i).val`.
