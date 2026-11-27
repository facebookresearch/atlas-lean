# Ben-Or: depth-three formulas for elementary symmetric polynomials

Let $\mathbb{F}$ have at least $n + 1$ elements. For every $0 \le d \le n$, the elementary symmetric polynomial $e_d(x_1, \dots, x_n)$ is computed by a $\Sigma\Pi\Sigma$ formula of size $O(n^2)$:

$$
e_d(x) = \sum_{j=0}^{n} c_{d,j} \prod_{i=1}^{n} (1 + \alpha_j x_i),
$$

for distinct $\alpha_0, \dots, \alpha_n \in \mathbb{F}$ and constants $c_{d,j}$ obtained by inverting the Vandermonde matrix $(\alpha_j^{d})_{j,d}$.

## Proof sketch

The univariate polynomial $\prod_i (1 + t x_i) = \sum_{d=0}^{n} e_d(x) t^d$ has degree $n$ in $t$, so its coefficients are determined by its values at $n+1$ distinct points $t = \alpha_j$ through a fixed linear map, the inverse Vandermonde matrix. Each evaluation is a product of $n$ affine linear forms.

## Depends on

- [Constant-depth arithmetic formulas with unbounded fan-in (arithmetic AC0)](constant-depth-arithmetic-formula.md)

## Sources

- M. Ben-Or, as presented in A. Shpilka, A. Wigderson, "Depth-3 arithmetic circuits over fields of characteristic zero", Computational Complexity 10 (2001) 1-27.
- A. Shpilka, A. Yehudayoff, "Arithmetic circuits: a survey of recent results and open questions", Foundations and Trends in Theoretical Computer Science 5 (2010).
