# Transitivity of inflation, restriction and corestriction

Let $G$ be a profinite group and $A$ a discrete $G$-module. For every $n \ge 0$, on
[cohomology](../cohomology-with-discrete-coefficients.md):

1. for closed normal subgroups $H \subseteq F$ of $G$,
   $\inf^{G/H}_G \circ \inf^{G/F}_{G/H} = \inf^{G/F}_G$, where $F/H$ is a closed normal subgroup of $G/H$ and
   $(G/H)/(F/H) = G/F$, $(A^H)^{F/H} = A^F$;
2. for closed subgroups $F \subseteq H$ of $G$, $\operatorname{res}^H_F \circ \operatorname{res}^G_H =
   \operatorname{res}^G_F$;
3. for open subgroups $F \subseteq H$ of $G$, $\operatorname{cor}^H_G \circ \operatorname{cor}^F_H =
   \operatorname{cor}^F_G$.

## Depends on

- [Inflation, restriction and conjugation](inflation-restriction-and-conjugation.md), for $\inf$ and
  $\operatorname{res}$
- [Corestriction for open subgroups](corestriction.md), for $\operatorname{cor}$

## Proof depends on

- [Cohomology commutes with direct limits](../cohomology-commutes-with-direct-limits.md), for the compatibility of
  the maps induced by compatible pairs with composition, which gives 1 and 2
- [The cochain formula for corestriction](cochain-formula-for-corestriction.md), for $\operatorname{cor}$ as the
  homology of the norm on the standard resolution, where $N_{G/H} \circ N_{H/F} = N_{G/F}$ gives 3

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §5, 2. Inflation, 3. Restriction and
  4. Corestriction, the transitivity formulas, p. 47.
