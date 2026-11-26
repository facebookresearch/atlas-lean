# Constant-depth formulas for power sums of roots

Let $\mathbb{F}$ be a field of characteristic $0$ or larger than $n$, and let $f(t) = \prod_{i=1}^{n}(t - r_i) = t^n + a_{n-1}t^{n-1} + \cdots + a_0$. For every $k \le \operatorname{poly}(n)$, the power sum $p_k = \sum_{i=1}^{n} r_i^k$ is computed from the coefficients $a_0, \dots, a_{n-1}$ by a constant-depth arithmetic formula of size $\operatorname{poly}(n, k)$. Conversely, the coefficients are computed from $p_1, \dots, p_n$ by a constant-depth formula of size $\operatorname{poly}(n)$.

## Proof sketch

Both directions use the logarithmic derivative identity $t f'(t)/f(t) = \sum_k p_k t^{-k}$ and $\log$ and $\exp$ of formal power series truncated at degree $k$. A truncated power series $\log(1 + g)$ or $\exp(g)$ with $g$ having zero constant term is a polynomial of degree $k$ in the coefficients of $g$; each coefficient is a sum over compositions, which can be written in constant depth by interpolating the univariate polynomials $(1 + yg)^{j}$ at $\operatorname{poly}(k)$ points and recombining linearly.

## Depends on

- [Constant-depth arithmetic formulas with unbounded fan-in (arithmetic AC0)](constant-depth-arithmetic-formula.md)

## Sources

- R. Andrews, A. Wigderson, "Constant-depth arithmetic circuits for linear algebra problems", FOCS (2024), arXiv:2404.10839.
