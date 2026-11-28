# The five term exact sequence

Let $G$ be a profinite group, $H$ a closed normal subgroup and $A$ a discrete $G$-module. With the
[inflation, restriction and transgression](inflation-restriction-and-corestriction.md) maps, the sequence

$$
0 \to H^1(G/H, A^H) \xrightarrow{\inf} H^1(G, A) \xrightarrow{\operatorname{res}} H^1(H, A)^{G/H}
\xrightarrow{\operatorname{tg}} H^2(G/H, A^H) \xrightarrow{\inf} H^2(G, A)
$$

of [cohomology](cohomology-with-discrete-coefficients.md) groups is exact. Moreover, if $n \ge 1$ and
$H^i(H, A) = 0$ for $i = 1, \dots, n - 1$, the sequence

$$
0 \to H^n(G/H, A^H) \xrightarrow{\inf} H^n(G, A) \xrightarrow{\operatorname{res}} H^n(H, A)^{G/H}
\xrightarrow{\operatorname{tg}} H^{n+1}(G/H, A^H) \xrightarrow{\inf} H^{n+1}(G, A)
$$

is exact. In particular inflation followed by restriction is exact at $H^n(G, A)$ in these cases.

For abstract groups and representations, Mathlib has the degree-one case, the exactness of the short complex
`groupCohomology.H1InfRes A S` of inflation and restriction for a normal subgroup `S`
(`groupCohomology.H1InfRes_exact`).

## Depends on

- [Inflation, restriction and corestriction for profinite groups](inflation-restriction-and-corestriction.md),
  for $\inf$, $\operatorname{res}$, the action of $G/H$ on $H^n(H, A)$ and the transgression
- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the cohomology groups

## Proof depends on

- [Inflation, restriction and corestriction for profinite groups](inflation-restriction-and-corestriction.md),
  for the cochain description of the transgression (Proposition (1.6.6)) used in the proof

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §6, Proposition (1.6.7) (Five Term
  Exact Sequence), p. 67.
