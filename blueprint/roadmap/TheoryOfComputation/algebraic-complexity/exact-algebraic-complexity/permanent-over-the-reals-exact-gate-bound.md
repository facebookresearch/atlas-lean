# Exact gate bound for the permanent over the reals

On an $m\times m$ array of independent variables, write $P_m=\sum_{\sigma\in S_m}\prod_i x_{\sigma(i),i}$. There are $c>0$ and $m_0\in\mathbb N$ such that for all $m\ge m_0$ and natural $s$, an exact gate-list circuit of size at most $s$ for $P_m$ over $\mathbb R$ requires $s>m^{c(\log_2 m)^{1/3}}$.

## Depends on

- [Gate-list circuits](gate-lists-for-polynomial-families.md)

## Proof depends on

- [Family of exact gate bounds](hamiltonian-cycle-and-permanent-exact-gate-bound.md)

## Proof outline

Use the exact gate bound in characteristic zero and instantiate the field with the reals after identifying its circuit representation.

## Sources

- Anthropic, [Solution.permanent_over_real](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Challenge.lean#L29-L31).
