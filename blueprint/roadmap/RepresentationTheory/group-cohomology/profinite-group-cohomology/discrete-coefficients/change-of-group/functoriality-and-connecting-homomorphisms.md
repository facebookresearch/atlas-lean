# Functoriality and the connecting homomorphisms

Let $G$ be a profinite group. The maps $\sigma_*$, $\inf$, $\operatorname{res}$
([Inflation, restriction and conjugation](inflation-restriction-and-conjugation.md)) and $\operatorname{cor}$
([Corestriction for open subgroups](corestriction.md)) of
[cohomology](../cohomology-with-discrete-coefficients.md) groups are natural in the discrete $G$-module, and they
commute with the connecting homomorphisms $\delta$ of the
[long exact cohomology sequence](../long-exact-cohomology-sequence.md): for an exact sequence
$0 \to A'' \to A \to A' \to 0$ of discrete $G$-modules and every $n \ge 0$,

$$
\delta \circ \operatorname{res} = \operatorname{res} \circ \delta, \qquad
\delta \circ \operatorname{cor} = \operatorname{cor} \circ \delta, \qquad
\delta \circ \sigma_* = \sigma_* \circ \delta,
$$

for a closed subgroup (an open subgroup for $\operatorname{cor}$, a closed subgroup $H$ and an exact sequence of
$H$-modules for $\sigma_*$), and $\delta \circ \inf = \inf \circ \delta$ for a closed normal subgroup $H$ such that
$0 \to A''^H \to A^H \to A'^H \to 0$ is also exact.

## Depends on

- [Inflation, restriction and conjugation](inflation-restriction-and-conjugation.md), for $\sigma_*$, $\inf$ and
  $\operatorname{res}$
- [Corestriction for open subgroups](corestriction.md), for $\operatorname{cor}$
- [The long exact cohomology sequence](../long-exact-cohomology-sequence.md), for $\delta$

## Proof depends on

- [The long exact cohomology sequence](../long-exact-cohomology-sequence.md), for the cochain-level description of
  $\delta$, with which maps induced by cochain maps commute
- [The cochain formula for corestriction](cochain-formula-for-corestriction.md), for $\operatorname{cor}$ as a map
  of cochain complexes

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §5, Proposition (1.5.2) with its
  proof, pp. 48–49.
