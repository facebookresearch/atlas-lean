# Hilbert's Theorem 90 for Galois extensions

Let $L|K$ be a Galois extension of fields, finite or infinite, and $G = G(L|K)$ its Galois group, a profinite group
with the Krull topology (Mathlib's `krullTopology`). The multiplicative group $L^\times$ is a discrete $G$-module, and

$$
H^1(G, L^\times) = 1
$$

for the [cohomology](cohomology-with-discrete-coefficients.md) of $G$.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  $H^1(G, L^\times)$

## Proof depends on

- [Cohomology as a direct limit over finite quotients](cohomology-as-a-direct-limit-over-finite-quotients.md),
  which reduces the statement to finite Galois extensions, the open normal subgroups of $G$ being the groups
  $G(L|L')$ of the finite Galois subextensions $L'|K$, with $(L^\times)^{G(L|L')} = L'^\times$
- [Hilbert's Theorem 90 for the multiplicative group](../../../../FieldTheory/galois-theory/multiplicative-hilbert-s-theorem-90.md),
  for the finite Galois extensions $L'|K$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter VI, §2, the setting at its
  beginning, p. 343, and Theorem (6.2.1) (Hilbert's Satz 90) with its proof, p. 344.
