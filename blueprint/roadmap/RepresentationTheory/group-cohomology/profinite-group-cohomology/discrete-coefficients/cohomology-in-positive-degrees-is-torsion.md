# Cohomology in positive degrees is torsion

Let $G$ be a profinite group, $U$ an open subgroup and $n$ an integer, and assume that $G$ is finite or $n \ge 1$;
here $\hat H^n(G, A) = H^n(G, A)$ for $n \ge 1$ ([cohomology](cohomology-with-discrete-coefficients.md)), and
$\hat H^n$ is [Tate cohomology](../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md) when $G$ is
finite. Then for every discrete $G$-module $A$ with $\hat H^n(U, A) = 0$,

$$
(G : U)\, \hat H^n(G, A) = 0.
$$

In particular, if $G$ is finite, then $\hat H^n(G, A)$ is annihilated by the order of $G$, and it is finite if
moreover $A$ is finitely generated as a $\mathbb{Z}$-module. Consequently, for every profinite group $G$ and every
discrete $G$-module $A$, the groups $H^n(G, A)$, $n \ge 1$, are torsion groups.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  $H^n(G, A)$
- [Tate cohomology groups of a finite group](../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md),
  for $\hat H^n(G, A)$ when $G$ is finite

## Proof depends on

- [Inflation, restriction and corestriction for profinite groups](inflation-restriction-and-corestriction.md),
  for $\operatorname{cor} \circ \operatorname{res} = (G : U)$ (Corollary (1.5.7)), extended to Tate cohomology
  for finite $G$
- [Cohomology as a direct limit over finite quotients](cohomology-as-a-direct-limit-over-finite-quotients.md),
  for the torsion of $H^n(G, A)$ from that of the finite levels

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §6, Proposition (1.6.1) and the
  conclusion after it, p. 60.
