# Continuous cohomology as an inverse limit over finite levels

Let $G$ be a profinite group and $A$ a compact $G$-module with a presentation $A = \varprojlim_{n \in \mathbb{N}} A_n$
as a countable inverse limit of finite discrete $G$-modules. Let $i \ge 0$. If $H^i(G, A_n)$ is finite for all $n$,
then the natural map is an isomorphism of [continuous cohomology](continuous-cohomology.md) groups

$$
H^{i+1}_{\mathrm{cts}}(G, A) \xrightarrow{\ \sim\ } \varprojlim_n H^{i+1}(G, A_n).
$$

For example this applies to $H^1_{\mathrm{cts}}(G, A)$, and to $H^2_{\mathrm{cts}}(G, A)$ when $G$ is finitely
generated.

## Depends on

- [Continuous cohomology](continuous-cohomology.md), for $H^i_{\mathrm{cts}}(G, -)$, which for the discrete modules
  $A_n$ is $H^i(G, A_n)$

## Proof depends on

- [Continuous cohomology of a countable inverse limit of finite modules](continuous-cohomology-of-a-countable-inverse-limit.md),
  for the exact sequence with $\varprojlim^1_n H^i(G, A_n)$ on the left
- [Mittag-Leffler towers have vanishing first derived limit](mittag-leffler-towers-have-vanishing-lim-one.md),
  for the vanishing of $\varprojlim^1$ of a tower of finite groups

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter II, §7, Corollary (2.7.6) and the
  remark after it, p. 142.
