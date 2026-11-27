# Interpolation adds constant depth to arithmetic formulas

Let $\Phi(t, x)$ be a constant-depth arithmetic formula of size $s$ computing a polynomial of degree at most $D$ in an auxiliary variable $t$, over a field with more than $D$ elements. Then every coefficient $[t^{j}]\Phi$, $0 \le j \le D$, is computed by a constant-depth formula of size $O(sD)$ whose depth exceeds that of $\Phi$ by at most one (one extra addition layer). In particular, truncated power-series operations of constant composition depth applied to constant-depth formulas stay in arithmetic $\mathrm{AC}^0$ with polynomial overhead.

## Proof sketch

Evaluate $\Phi$ at $D + 1$ distinct field elements $\alpha_0, \dots, \alpha_D$ in place of $t$, obtaining $D+1$ copies of the formula, and combine them linearly using the rows of the inverse Vandermonde matrix; a linear combination is a single unbounded fan-in addition gate with constants on its edges.

## Depends on

- [Arithmetic AC0: constant-depth arithmetic circuits with division and piecewise computation](constant-depth-arithmetic-formula.md)

## Proof depends on

- [Ben-Or: depth-three formulas for elementary symmetric polynomials](benor-elementary-symmetric.md)

## Sources

- R. Andrews, A. Wigderson, "Constant-depth arithmetic circuits for linear algebra problems", FOCS (2024), arXiv:2404.10839.
- M. Ben-Or, as presented in A. Shpilka, A. Wigderson, "Depth-3 arithmetic circuits over fields of characteristic zero", Computational Complexity 10 (2001) 1-27.
