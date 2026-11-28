# Cohomology of a profinite group with discrete coefficients

Let $G$ be a profinite group and $A$ a discrete $G$-module: an abelian group, with the discrete topology, on which
$G$ acts continuously. For $n \ge 0$ let $X^n(G, A)$ be the group of continuous maps $x \colon G^{n+1} \to A$, a
$G$-module by

$$
(\sigma x)(\sigma_0, \dots, \sigma_n) = \sigma\, x(\sigma^{-1}\sigma_0, \dots, \sigma^{-1}\sigma_n),
$$

and let the homogeneous $n$-cochains $C^n(G, A) = X^n(G, A)^G$ be the continuous maps with
$x(\sigma\sigma_0, \dots, \sigma\sigma_n) = \sigma\, x(\sigma_0, \dots, \sigma_n)$ for all $\sigma \in G$. The
coboundary $\partial \colon C^{n-1}(G, A) \to C^n(G, A)$ is

$$
(\partial x)(\sigma_0, \dots, \sigma_n) = \sum_{i=0}^{n} (-1)^i\, x(\sigma_0, \dots, \widehat{\sigma_i}, \dots, \sigma_n),
$$

and $\partial \partial = 0$. With $Z^n(G, A) = \ker(\partial \colon C^n \to C^{n+1})$, $B^n(G, A) = \partial C^{n-1}(G, A)$
for $n \ge 1$ and $B^0(G, A) = 0$, the $n$-th cohomology group of $G$ with coefficients in $A$ is

$$
H^n(G, A) = Z^n(G, A) / B^n(G, A),
$$

so that $H^0(G, A) = A^G$. Equivalently one may use inhomogeneous cochains, the continuous maps $y \colon G^n \to A$,
through $y(\sigma_1, \dots, \sigma_n) = x(1, \sigma_1, \sigma_1\sigma_2, \dots, \sigma_1 \cdots \sigma_n)$.

$H^n(G, A)$ is the continuous cochain cohomology $H^n_{\mathrm{cts}}(G, A)$ of $A$ with its discrete topology
(Neukirch–Schmidt–Wingberg, the remark after (2.7.1)), that is
[continuous cohomology](../continuous-cochain-cohomology/continuous-cohomology.md) of $A$ as a topological
representation of $G$ over $\mathbb{Z}$ with the discrete topology; Mathlib writes its cochains in the curried
form $C(G, C(G, \dots, C(G, A)))$, which for the compact group $G$ is $C(G^{n+1}, A)$.

## Depends on

- [Continuous Module](../../../not-yet-classified/discrete-gmodules/continuous-module.md), for the discrete
  $G$-modules, the modules with a discrete continuous action (here over $\mathbb{Z}$)
- [Continuous cohomology](../continuous-cochain-cohomology/continuous-cohomology.md), for the continuous cochain
  cohomology that $H^n(G, A)$ is for a discrete module

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §2, pp. 12–14 (the standard
  resolution, homogeneous cochains, Definition (1.2.2) and the inhomogeneous cochains); Chapter II, §7, (2.7.1)
  and the remark after it, p. 137.
