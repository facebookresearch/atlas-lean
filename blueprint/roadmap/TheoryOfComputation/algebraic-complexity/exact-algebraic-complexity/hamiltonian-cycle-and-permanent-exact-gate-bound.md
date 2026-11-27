# Exact gate bounds for the Hamiltonian cycle polynomial and the permanent

On an $m\times m$ array of independent variables, write $H_m=\sum_\sigma\prod_i x_{i,\sigma(i)}$ summing over permutations that are one cycle on the entire index set, and $P_m=\sum_\sigma\prod_i x_{\sigma(i),i}$ summing over all permutations.

There is one real $c>0$ such that for every natural characteristic $p$ there is $m_0\in\mathbb N$ with the following property. Over every field of characteristic $p$, for every $m\ge m_0$ and natural $s$, if an exact circuit of size at most $s$ serves $H_m$, then $s>m^{c(\log_2 m)^{1/3}}$. If $p\ne 2$, an exact circuit serving $P_m$ has the same strict lower bound. The field may vary after the threshold is chosen; the permanent clause is absent in characteristic two.

## Depends on

- [Gate-list circuits](gate-lists-for-polynomial-families.md)

## Expansion

Separate the reductions that turn circuits for the Hamiltonian cycle polynomial and permanent into circuits for grid sums from the two characteristic-dependent grid-sum bounds (the flat and contracting cases). State a reusable same-characteristic transfer for exact gate lists computing polynomials with integral coefficients, preserving the gate bound. Use that transfer to assemble the two bounds over arbitrary fields, with a threshold allowed to depend on the characteristic and the permanent clause restricted to characteristic other than two.

## Sources

- Anthropic, [Solution.mainTheorem](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Challenge.lean#L17-L18).
- [Exact lower-bound proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L20-L46).
- [The grid-sum cases and the transfer between fields](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Fields.lean#L50-L110).
