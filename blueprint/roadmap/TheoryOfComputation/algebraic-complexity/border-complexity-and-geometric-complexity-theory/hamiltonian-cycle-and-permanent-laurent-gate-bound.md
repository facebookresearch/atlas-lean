# Laurent-series approximation bounds for the Hamiltonian cycle polynomial and the permanent

On an $m\times m$ array of independent variables, write $H_m=\sum_\sigma\prod_i x_{i,\sigma(i)}$ summing over permutations that are one cycle on the entire index set, and $P_m=\sum_\sigma\prod_i x_{\sigma(i),i}$ summing over all permutations.

There is one real $c>0$ such that for every natural characteristic $p$ there is $m_0\in\mathbb N$ with the following property. Over every field of characteristic $p$, for every $m\ge m_0$ and natural $s$, if a Laurent-series approximating circuit of size at most $s$ serves $H_m$, then $s>m^{c(\log_2 m)^{1/3}}$. If $p\ne 2$, a Laurent-series approximating circuit serving $P_m$ has the same strict lower bound. The field may vary after the threshold is chosen; the permanent clause is absent in characteristic two.

## Depends on

- [Laurent-series approximating circuits](../exact-algebraic-complexity/gate-lists-for-polynomial-families.md)

## Expansion

Separate the Laurent-series truncation lemma from the circuit lower bound: approximate finitely many scalar series by Laurent polynomials while preserving all nonpositive coefficients in products of a fixed number of those scalars. Then adapt the grid-sum lower bounds and reductions to the approximation condition, including the transfer of coefficient constraints between fields of the same characteristic. An exact gate bound alone does not give that transfer or the approximate grid-sum bound.

## Sources

- Anthropic, [Solution.mainTheoremApprox](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Challenge.lean#L20-L21).
- [Approximation and its lower-bound proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L50-L60).
- [Truncation of Laurent-series constants](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Approximate.lean#L96-L113) and [the approximate lower bounds and their transfer](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Approximate.lean#L179-L300).
