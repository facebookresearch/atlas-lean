# Finite-variable logics $\mathrm{FO}^k$ and $L^k_{\infty\omega}$

For $k \ge 1$, the *$k$-variable fragment* $\mathrm{FO}^k$ consists of the first-order formulas all of whose variables (free and bound) are among $x_1,\dots,x_k$; a variable may be requantified inside its own scope. The *infinitary $k$-variable logic* $L^k_{\infty\omega}$ closes the $k$-variable formulas under conjunctions and disjunctions of arbitrary sets of formulas, still with all variables among $x_1,\dots,x_k$. For example, on linear orders the $\mathrm{FO}^2$ formulas $\varphi_1(x) = \exists y\,(y > x)$, $\varphi_{m+1}(x) = \exists y\,(y > x \wedge \varphi_m(y))$, with the roles of $x$ and $y$ swapped at each step, say that at least $m$ elements lie above $x$, for every $m\ge1$.

## Depends on

- [Quantifier rank and rank-$n$ equivalence](../finite-structures-and-definability/quantifier-rank.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- N. Immerman, Descriptive Complexity, Springer, 1999.
