# Instances of SHORTEST PATH with negative lengths

An instance of SHORTEST PATH with negative lengths is a value of type `ℕ × List (ℕ × ℕ × (ℕ × ℕ)) × (ℕ × ℕ) × ℕ × ℕ`: vertex count `n` (vertices `Fin n`), the edge list with lengths (an entry `(u, v, (l⁺, l⁻))` is the edge `{u, v}` of length `l⁺ - l⁻`), the bound `K` as `(K⁺, K⁻)`, with `K = K⁺ - K⁻`, and the endpoints `s` and `t`.
