# Geometric domination of series terms

Let `a` be majorized by a geometric majorant `m` with bound `M` and radii
`R_i`, and let `x ∈ ℝ^d` satisfy `|x i| ≤ b i` for some `b : Fin d → ℚ≥0`.
Then for every exponent `α`, `|coeff α a · ∏ i, x i ^ α i| ≤ M ∏ i, q_i ^ α
i` with `q_i = b_i / R_i`.

Here `a` is a formal power series in `d` variables with rational
coefficients, its sum at `x ∈ ℝ^d` is `∑' α, coeff α a · ∏ i, x i ^ α i`,
and its rectangular sum for `N : Fin d → ℕ` is the finite sum of the same
terms over exponents with `α i < N i` for all `i`. A geometric majorant `m`
with bound `M ≥ 0` and radii `R_i > 0` majorizes `a` when `|coeff α a| ≤ M ∏
i, R_i ^ (-α i)` for every `α`, and `q_i = b_i / R_i`.
