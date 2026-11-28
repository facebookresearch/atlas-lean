# Cohomology of a finite group with discrete coefficients

Let $G$ be a finite group, with the discrete topology, and $A$ a $G$-module, a discrete $G$-module for the discrete
topology on $A$. Every map $G^{n+1} \to A$ is continuous, so the cochains of the
[cohomology with discrete coefficients](cohomology-with-discrete-coefficients.md) are all homogeneous cochains, and
for every $n \ge 0$ its cohomology group $H^n(G, A)$ is isomorphic to Mathlib's group cohomology
`groupCohomology (Rep.of ρ) n` of $A$ as a $\mathbb{Z}$-linear representation $\rho$ of $G$, naturally in $A$ and
compatibly with the connecting homomorphisms. Consequently, for $n \ge 1$, $H^n(G, A)$ is isomorphic to the
[Tate cohomology](../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md) group $\hat H^n(G, A)$
(`TateCohomology.isoGroupCohomology`).

## Depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  $H^n(G, A)$
- [Tate cohomology groups of a finite group](../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md),
  for $\hat H^n(G, A)$

## Proof depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for the
  inhomogeneous cochains, which for a discrete group are Mathlib's inhomogeneous cochains
  `groupCohomology.inhomogeneousCochains`

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §6, the opening paragraph, p. 60
  ("for $n \ge 1$ this means, as for finite groups, $\hat H^n(G, A) = H^n(G, A)$").
