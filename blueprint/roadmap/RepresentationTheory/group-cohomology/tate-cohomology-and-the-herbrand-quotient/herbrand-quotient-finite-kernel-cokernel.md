# Herbrand quotients agree across a map with finite kernel and cokernel

Let $G$ be a finite cyclic group and let $\alpha \colon M \to N$ be a homomorphism of $G$-modules, that
is, of $\mathbb{Z}$-linear representations of $G$, whose kernel and cokernel are finite. If one of the
Herbrand quotients $h(M)$ and $h(N)$ is defined, that is, if the Tate cohomology groups
$\hat H^0(G, \cdot)$ and $\hat H^{-1}(G, \cdot)$ of $M$, or those of $N$, are finite, then so is the
other, and

$$h(M) = h(N), \qquad h(X) = |\hat H^0(G, X)| / |\hat H^{-1}(G, X)|.$$

In particular, every finite $G$-module $M$ has $h(M) = 1$: apply the statement to $M \to 0$.

Milne first proves the case of a finite module: for a generator $g$ of $G$, the exact sequence
$0 \to M^G \to M \xrightarrow{g - 1} M \to M_G \to 0$ shows that the invariants $M^G$ and the coinvariants
$M_G$ have the same order, and the norm map $M_G \to M^G$ has kernel $\hat H^{-1}(G, M)$ and cokernel
$\hat H^0(G, M)$. The general case applies the
[multiplicativity of the Herbrand quotient](herbrand-quotient-mul-of-short-exact.md) to
$0 \to \alpha(M) \to N \to \mathrm{Coker}(\alpha) \to 0$ and to
$0 \to \mathrm{Ker}(\alpha) \to M \to \alpha(M) \to 0$. Milne's Herbrand quotient divides by
$|H^1(G, X)|$ instead of $|\hat H^{-1}(G, X)|$; for cyclic $G$ the two groups are isomorphic by the
[periodicity of Tate cohomology](nonempty-periodicity-iso.md), so the two quotients agree.

## Depends on

- [Herbrand quotient](herbrand-quotient.md)

## Proof depends on

- [Multiplicativity of the Herbrand quotient in short exact sequences](herbrand-quotient-mul-of-short-exact.md)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>, Chapter II, §3: the definition of the Herbrand
  quotient before Proposition 3.6, Proposition 3.6 (multiplicativity), Proposition 3.8 (a finite module
  has Herbrand quotient $1$) and Corollary 3.9 (the statement).
