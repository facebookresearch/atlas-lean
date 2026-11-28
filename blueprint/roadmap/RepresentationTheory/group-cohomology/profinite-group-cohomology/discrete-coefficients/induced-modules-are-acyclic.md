# Induced modules are acyclic

Let $G$ be a profinite group and $A$ a discrete $G$-module. The induced module $\operatorname{Ind}_G(A)$ is the
group of continuous maps $x \colon G \to A$ ($A$ discrete), with the action $(\sigma x)(\tau) = \sigma\, x(\sigma^{-1}\tau)$;
it is a discrete $G$-module. A discrete $G$-module $M$ is acyclic if $H^n(G, M) = 0$ for all $n > 0$.

Then $\operatorname{Ind}_G(A)$ is acyclic:

$$
H^n(G, \operatorname{Ind}_G(A)) = 0 \quad \text{for all } n > 0,
$$

for the [cohomology](cohomology-with-discrete-coefficients.md) of $G$. If $G$ is finite, moreover
$\hat H^n(G, \operatorname{Ind}_G(A)) = 0$ for all $n \in \mathbb{Z}$, for the
[Tate cohomology](../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md) of $G$.

Neukirch–Schmidt–Wingberg deduce from this, with Proposition (1.3.6)(ii), that $\operatorname{Ind}_G(A)$ is
[cohomologically trivial](induced-modules-are-cohomologically-trivial.md): $H^n(H, \operatorname{Ind}_G(A)) = 0$
for every closed subgroup $H$ and all $n > 0$.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  $H^n(G, -)$
- [Tate cohomology groups of a finite group](../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md),
  for $\hat H^n(G, -)$ when $G$ is finite

## Proof depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the isomorphism of the complex $X^\bullet(G, \operatorname{Ind}_G(A))^G$ with the standard resolution
  $X^\bullet(G, A)$, which is exact (Proposition (1.2.1))

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §2, Proposition (1.2.1), p. 12;
  §3, Definition (1.3.5) and the induced modules after it, p. 31, and Proposition (1.3.7) with its proof,
  p. 32.
