# The transgression

Let $G$ be a profinite group, $H$ a closed normal subgroup and $A$ a discrete $G$-module, and let $G/H$ act on
$H^1(H, A)$ as in
[The action of the quotient on the cohomology of a normal subgroup](action-of-the-quotient-on-the-cohomology-of-a-normal-subgroup.md).
If $x \colon H \to A$ is an inhomogeneous $1$-cocycle whose class lies in $H^1(H, A)^{G/H}$, there is a continuous
$1$-cochain $y \colon G \to A$ with $y|_H = x$ such that $(\partial y)(\sigma_1, \sigma_2)$ lies in $A^H$ and depends
only on the cosets $\sigma_1 H$, $\sigma_2 H$, so that $\partial y$ is a $2$-cocycle of $G/H$ with values in $A^H$;
and for any two such cochains the classes of $\partial y$ in $H^2(G/H, A^H)$ agree. The transgression is the
homomorphism

$$
\operatorname{tg} \colon H^1(H, A)^{G/H} \longrightarrow H^2(G/H, A^H), \qquad \operatorname{tg}[x] = [\partial y],
$$

of [cohomology](../cohomology-with-discrete-coefficients.md) groups, in inhomogeneous cochains.

## Depends on

- [The action of the quotient on the cohomology of a normal subgroup](action-of-the-quotient-on-the-cohomology-of-a-normal-subgroup.md),
  for the invariants $H^1(H, A)^{G/H}$
- [Cohomology of a profinite group with discrete coefficients](../cohomology-with-discrete-coefficients.md), for
  the inhomogeneous cochains

## Proof depends on

- [Cohomology of a profinite group with discrete coefficients](../cohomology-with-discrete-coefficients.md), for
  the cochain computations of the proof, which uses a continuous section $s \colon G/H \to G$ of the projection with
  $s(1) = 1$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §6, Proposition (1.6.6) with its
  proof, pp. 65–66; the continuous section is Chapter I, §1, Exercise 4.
