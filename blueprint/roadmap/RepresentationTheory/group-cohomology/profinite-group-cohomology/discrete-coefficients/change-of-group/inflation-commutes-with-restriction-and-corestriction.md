# Inflation commutes with restriction and corestriction

Let $G$ be a profinite group, $A$ a discrete $G$-module and $V \subseteq U \subseteq G$ closed subgroups. On
[cohomology](../cohomology-with-discrete-coefficients.md), for every $n \ge 0$:

1. if $V$ is normal in $G$, then

    $$
    \inf^{U/V}_U \circ \operatorname{res}^{G/V}_{U/V} = \operatorname{res}^G_U \circ \inf^{G/V}_G \colon
    H^n(G/V, A^V) \longrightarrow H^n(U, A);
    $$

2. if $V$ is normal in $G$ and $U$ is open in $G$, then

    $$
    \inf^{G/V}_G \circ \operatorname{cor}^{U/V}_{G/V} = \operatorname{cor}^U_G \circ \inf^{U/V}_U \colon
    H^n(U/V, A^V) \longrightarrow H^n(G, A).
    $$

## Depends on

- [Inflation, restriction and conjugation](inflation-restriction-and-conjugation.md), for $\inf$ and
  $\operatorname{res}$
- [Corestriction for open subgroups](corestriction.md), for $\operatorname{cor}$

## Proof depends on

- [Cohomology commutes with direct limits](../cohomology-commutes-with-direct-limits.md), for the compatibility of
  the maps induced by compatible pairs with composition, which gives 1
- [The cochain formula for corestriction](cochain-formula-for-corestriction.md), for the cochain-level computation
  in 2, the representatives of $U \backslash G$ serving for $(U/V) \backslash (G/V)$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §5, Proposition (1.5.5), p. 50, and
  the remark after it that all this can be seen on the level of cochains, p. 51.
