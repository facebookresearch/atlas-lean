# Homogeneous prism vertices

For a type `X`, `n : ℕ`, tuples `a,b : Fin (n + 1) → X`, and `i : Fin (n + 1)`, the tuple
`vertices a b i : Fin (n + 2) → X` has entries `a_j` for `j ≤ i` and `b_{j-1}` for `j > i`.
Thus its ordered vertices are `(a₀,…,a_i,b_i,…,b_n)`.
