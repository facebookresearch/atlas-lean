# Jerrum-Sinclair-Vigoda: FPRAS for the permanent

For a bitstring $x$, let
$\operatorname{perm}(x)$ be the permanent of the 0-1 matrix encoded by $x$: if $x$ decodes, under
the canonical bitstring encoding, to a pair $(k, e)$ of a natural number $k$ and a list $e$ of
$k^2$ natural numbers each at most $1$, then $\operatorname{perm}(x)$ is the permanent of the
$k \times k$ matrix with row-major entries $e$, and otherwise $\operatorname{perm}(x) = 0$. There
are a polynomial $p$ with natural-number coefficients and a polynomial-time computable function
$E$ from triples of bitstrings to natural numbers such that for all bitstrings $x$ and $w$ with
$n = |w| \ge 1$ (the precision, given in unary), at least two thirds of the bitstrings $r$ of
length $p(|x| + n)$ satisfy
$|E(x, r, w) - \operatorname{perm}(x)| \le \operatorname{perm}(x) / n$.

## Sources

- M. Jerrum, A. Sinclair, and E. Vigoda, "A polynomial-time approximation algorithm for the permanent of a matrix with nonnegative entries", Journal of the ACM 51 (2004), 671-697 (STOC 2001); M. Jerrum and A. Sinclair, "Approximating the permanent", SIAM Journal on Computing 18 (1989), 1149-1178 (precursor with restricted guarantees).
