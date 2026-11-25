# Uniform rectangular truncation bound

Let `a` be majorized by a geometric majorant `m`, let `b : Fin d → ℚ≥0`
satisfy `b i < R_i` for every `i`, and let `x ∈ ℝ^d` lie in the box `|x i| ≤
b i`. Then for every `N : Fin d → ℕ`, the sum of `a` at `x` and its
rectangular sum differ by at most `M (∑ i, q_i ^ N_i) ∏ i, (1 - q_i)⁻¹`.

Here `a` is a formal power series in `d` variables with rational
coefficients, its sum at `x ∈ ℝ^d` is `∑' α, coeff α a · ∏ i, x i ^ α i`,
and its rectangular sum for `N : Fin d → ℕ` is the finite sum of the same
terms over exponents with `α i < N i` for all `i`. A geometric majorant `m`
with bound `M ≥ 0` and radii `R_i > 0` majorizes `a` when `|coeff α a| ≤ M ∏
i, R_i ^ (-α i)` for every `α`, and `q_i = b_i / R_i`.
