# Cohomology as a direct limit over finite quotients

Let $G$ be a profinite group and $A$ a discrete $G$-module, with
[cohomology](cohomology-with-discrete-coefficients.md) $H^n(G, A)$. Let $U, V$ run through the open normal subgroups
of $G$. For $V \subseteq U$ the projections $G^{n+1} \to (G/V)^{n+1} \to (G/U)^{n+1}$ induce homomorphisms of
cochain complexes $C^\bullet(G/U, A^U) \to C^\bullet(G/V, A^V) \to C^\bullet(G, A)$, hence homomorphisms

$$
H^n(G/U, A^U) \longrightarrow H^n(G/V, A^V) \longrightarrow H^n(G, A),
$$

where the finite group $G/U$ acts on $A^U$. The groups $H^n(G/U, A^U)$ form a direct system, and for every
$n \ge 0$ the canonical homomorphism

$$
\varinjlim_U H^n(G/U, A^U) \longrightarrow H^n(G, A)
$$

is an isomorphism. Already $\varinjlim_U C^\bullet(G/U, A^U) \to C^\bullet(G, A)$ is an isomorphism of complexes,
since a continuous cochain with values in the discrete module $A$ is locally constant.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  $H^n(G, A)$ and its cochains, for $G$ and for the finite quotients $G/U$

## Proof depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the cochain complexes compared in the proof

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §2, the construction before
  Proposition (1.2.5), p. 20, and Proposition (1.2.5) with its proof, pp. 21–22.
