# Cohomology of torsion-free procyclic groups

Let $S$ be a set of prime numbers and $G = \prod_{p \in S} \mathbb{Z}_p$, a torsion-free procyclic group, with a
topological generator $\sigma$; for $S$ the set of all primes, $G = \hat{\mathbb{Z}}$. Let $\mathbb{N}(S)$ be the set
of natural numbers divisible by no prime outside $S$. An abelian group $X$ is $S$-divisible if $X = nX$ for all
$n \in \mathbb{N}(S)$, and $S$-torsion if $X = \bigcup_{n \in \mathbb{N}(S)} {}_nX$, where ${}_nX = \{x \in X : nx = 0\}$.
Let $A$ be a discrete $G$-module and $N_n = 1 + \sigma + \dots + \sigma^{n-1}$. For the
[cohomology](cohomology-with-discrete-coefficients.md) of $G$:

1. $H^1(G, A) \cong A_0 / (\sigma - 1)A$, where $A_0 = \{a \in A : N_n a = 0 \text{ for some } n \in \mathbb{N}(S)\}$,
   the isomorphism sending the class of an inhomogeneous $1$-cocycle $x \colon G \to A$ to the class of $x(\sigma)$.
   If $A$ is $S$-torsion, then $A_0 = A$ and so $H^1(G, A) \cong A_G = A/(\sigma - 1)A$.
2. If $A$ is torsion or $S$-divisible, then $H^n(G, A) = 0$ for all $n \ge 2$.

In particular, for $G = \hat{\mathbb{Z}}$ and a finite discrete module $A$, $H^0(G, A) = A^G = \ker(\sigma - 1)$ and
$H^1(G, A) \cong \operatorname{coker}(\sigma - 1)$ have the same order, and $H^n(G, A) = 0$ for $n \ge 2$. For the
trivial module $\mathbb{Z}$, which is not $S$-torsion, $A_0 = 0$ and $H^1(G, \mathbb{Z}) = 0$.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  $H^n(G, A)$ and the inhomogeneous cocycles
- [The ring of p-adic integers](../../../../NumberTheory/p-adic-numbers/p-adic-integers.md), for the groups
  $\mathbb{Z}_p$

## Proof depends on

- [Cohomology as a direct limit over finite quotients](cohomology-as-a-direct-limit-over-finite-quotients.md),
  for $H^n(G, A) = \varinjlim_n H^n(G/G^n, A^{G^n})$ over $n \in \mathbb{N}(S)$
- [Periodicity of Tate cohomology for finite cyclic groups](../../tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md),
  for the cohomology of the finite cyclic quotients $G/G^n$ (Neukirch–Schmidt–Wingberg (1.7.1))
- [Cohomology commutes with direct limits](cohomology-commutes-with-direct-limits.md), for the passage from
  finite to torsion modules
- [Induced modules are acyclic](induced-modules-are-acyclic.md) and
  [the long exact cohomology sequence](long-exact-cohomology-sequence.md), for the dimension shifting in (2)
- [Cohomology in positive degrees is torsion](cohomology-in-positive-degrees-is-torsion.md), for the $S$-divisible
  case of (2)

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §7, the procyclic groups before
  Proposition (1.7.7), and Proposition (1.7.7) with its proof, pp. 78–79.
