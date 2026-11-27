# Step bound of the SAT verifier machine

For a flag $\mathit{cap}$, let $p$ be the
per-step push budget of the host machine with that flag (the sum over its labels of the number
of push instructions in each label's statement). The step bound is the polynomial
$(p + 1)(8X^2 + 15X + 10) + X + 2$ with natural-number coefficients, in the input length $X$.
