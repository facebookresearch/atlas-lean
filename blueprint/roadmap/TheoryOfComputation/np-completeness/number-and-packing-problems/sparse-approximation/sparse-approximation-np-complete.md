# SPARSE APPROXIMATION is NP-complete

The SPARSE APPROXIMATION decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a matrix `A ∈ ℚ^{m × n}`, a vector `b ∈ ℚ^m`, a rational `ε > 0`, and a nonnegative integer `k`. Question: is there a vector `x ∈ ℝ^n` with at most `k` nonzero entries and `‖Ax - b‖₂ ≤ ε`?

## Sources

- B. K. Natarajan, "Sparse approximate solutions to linear systems", SIAM Journal on Computing 24 (1995), 227-234, doi:10.1137/S0097539792240406.
