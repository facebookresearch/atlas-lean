# Cohomology commutes with direct limits

Let $G$ and $G'$ be profinite groups, $A$ a discrete $G$-module and $A'$ a discrete $G'$-module. A compatible pair is
a pair of homomorphisms $\varphi \colon G' \to G$ (continuous) and $f \colon A \to A'$ with
$f(\varphi(\sigma')a) = \sigma' f(a)$; it induces $C^n(G, A) \to C^n(G', A')$, $x \mapsto f \circ x \circ \varphi$, and
so homomorphisms $H^n(G, A) \to H^n(G', A')$ of [cohomology](cohomology-with-discrete-coefficients.md),
compatible with composition of compatible pairs.

Let $(G_i)_{i \in I}$ be a projective system of profinite groups and $(A_i)_{i \in I}$ a direct system, over the
same directed set $I$, where each $A_i$ is a discrete $G_i$-module and for $i \le j$ the transition maps
$G_j \to G_i$ and $A_i \to A_j$ form compatible pairs. Then the groups $H^n(G_i, A_i)$ form a direct system, and for
$G = \varprojlim_i G_i$ and $A = \varinjlim_i A_i$ (a discrete $G$-module) the induced maps give, for every
$n \ge 0$, an isomorphism

$$
H^n(G, A) \cong \varinjlim_{i \in I} H^n(G_i, A_i).
$$

In particular, for a constant system $G_i = G$, the cohomology of $G$ commutes with direct limits of discrete
$G$-modules: $H^n(G, \varinjlim_i A_i) = \varinjlim_i H^n(G, A_i)$.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the cohomology groups and their cochains

## Proof depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the cochain-level comparison $\varinjlim_i C^n(G_i, A_i) \to C^n(G, A)$ in the proof

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §5, the compatible pairs before
  Proposition (1.5.1) and Proposition (1.5.1), p. 45.
