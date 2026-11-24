# Cup products in Tate cohomology

This node is still to be broken down. It covers the cup products on the cohomology and the
[Tate cohomology](tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md) of a finite group that Tate's theorem uses. Let $G$ be a group and $M, N$
$G$-modules, with $G$ acting diagonally on $M \otimes N$.

- **Cup products.** There are pairings $H^r(G, M) \times H^s(G, N) \to H^{r+s}(G, M \otimes N)$, given on inhomogeneous
  cochains by $(f \cup g)(g_1, \dots, g_{r+s}) = f(g_1, \dots, g_r) \otimes g_1 \cdots g_r\, g(g_{r+1}, \dots, g_{r+s})$,
  natural in $M$ and $N$, associative and graded commutative, compatible with the connecting homomorphisms of exact
  sequences, and in degree $0$ given by $m \otimes n \mapsto m \otimes n$.
- **Tate cohomology.** When $G$ is finite, the cup products extend uniquely to pairings
  $\hat H^r(G, M) \times \hat H^s(G, N) \to \hat H^{r+s}(G, M \otimes N)$ for all $r, s \in \mathbb{Z}$ with the same properties.

## Expansion

A good expansion has definition pages for the cup products on cohomology and on Tate cohomology and statement pages for
their properties, each citing the sources below with locators; Milne refers to Weiss for the extension to Tate
cohomology.

## Depends on

- [Tate cohomology groups of a finite group](tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md), for $\hat H^r(G, M)$

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020), <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Chapter II,
  §1, "Cup-products", p. 72 (the pairings, their description on cochains and their properties), and §3, "Cup-products",
  p. 80 ("When the group G is finite, the cup-products extend in a unique way to all the cohomology groups, and have the
  same list of properties. See Weiss 1969, Chapter IV").
- E. Weiss, *Cohomology of groups*, Academic Press, 1969, Chapter IV, as cited by Milne.
