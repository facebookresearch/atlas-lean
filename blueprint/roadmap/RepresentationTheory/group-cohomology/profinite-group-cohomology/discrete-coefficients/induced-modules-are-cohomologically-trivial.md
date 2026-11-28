# Induced modules are cohomologically trivial

This node is still to be broken down. Let $G$ be a profinite group and $A$ a discrete $G$-module. A discrete
$G$-module $M$ is cohomologically trivial if $H^n(H, M) = 0$ for all closed subgroups $H$ of $G$ and all $n > 0$.
The node states that the induced module $\operatorname{Ind}_G(A)$ is cohomologically trivial, and more generally
that so is every induced $G$-module, such as the modules $X^n(G, A) = \operatorname{Map}(G^{n+1}, A)$ of the standard
resolution, which are induced as $H$-modules for every closed subgroup $H$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- Proposition (1.3.6)(ii): an induced $G$-module is an induced $H$-module for every closed subgroup $H$ of $G$, and
  $A^H$ is an induced $G/H$-module when $H$ is normal; its proof uses a homeomorphism $G \cong H \times G/H$
  (Neukirch–Schmidt–Wingberg, Chapter I, §1, Exercise 4, as cited in the proof of (1.3.6));
- the passage from the [acyclicity of induced modules](induced-modules-are-acyclic.md) over $G$ to every closed
  subgroup $H$, as in the proof of (1.3.7).

## Depends on

- [Induced modules are acyclic](induced-modules-are-acyclic.md), for $\operatorname{Ind}_G(A)$ and acyclicity
- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the cohomology of the closed subgroups $H$

## Proof depends on

- [Induced modules are acyclic](induced-modules-are-acyclic.md), for the acyclicity over $G$, applied to $H$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §3, Definition (1.3.5) and
  Proposition (1.3.6), p. 31, and Proposition (1.3.7) with its proof, p. 32; Chapter I, §1, Exercise 4 is cited
  as Neukirch–Schmidt–Wingberg cite it in the proof of (1.3.6), not read here.
