# Vanishing of cohomology on modules uniquely divisible by the primes dividing the order

Let $G$ be a finite group and $A$ a $G$-module such that multiplication by $p$ is an automorphism of $A$ for every
prime number $p$ dividing $\#G$. Then

$$
\hat H^i(G, A) = 0 \quad \text{for all } i \in \mathbb{Z},
$$

for the [Tate cohomology](../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md) of $G$. If $G$ is
a profinite group and $A$ a discrete $G$-module such that multiplication by $p$ is an automorphism of $A$ for every
prime $p$ dividing the order of $G$ (the supernatural number $\#G$, divisible by $p$ when $p$ divides the index of
some open subgroup), then $H^i(G, A) = 0$ for all $i \ge 1$, for the
[cohomology](cohomology-with-discrete-coefficients.md) of $G$.

In particular this holds, and $A$ is cohomologically trivial, when $A$ is a torsion group whose supernatural
order is prime to $\#G$, and when $A$ is uniquely divisible, for instance a $\mathbb{Q}$-vector space: for every
profinite group $G$ and every discrete $G$-module $V$ that is a $\mathbb{Q}$-vector space, $H^i(G, V) = 0$ for
$i \ge 1$. (Neukirch–Schmidt–Wingberg also list abelian profinite groups of order prime to $\#G$, which are not
discrete modules.)

## Depends on

- [Tate cohomology groups of a finite group](../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md),
  for $\hat H^i(G, A)$
- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  $H^i(G, A)$ when $G$ is profinite

## Proof depends on

- [Cohomology in positive degrees is torsion](cohomology-in-positive-degrees-is-torsion.md), for the
  annihilation of $\hat H^i(G, A)$ by $\#G$, on which multiplication by $\#G$ is also an automorphism
- [Cohomology as a direct limit over finite quotients](cohomology-as-a-direct-limit-over-finite-quotients.md),
  for the passage from the finite quotients $G/U$, acting on $A^U$, to the profinite group $G$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §6, Proposition (1.6.2), cases
  a) and c), p. 60.
