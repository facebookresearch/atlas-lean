# Cup products in Tate cohomology

This node is still to be broken down. It covers the cup products on the cohomology and the
[Tate cohomology](tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md) of a finite group that Tate's theorem uses. Let $G$ be a group and $M, N$
$G$-modules, with $G$ acting diagonally on $M \otimes N$.

- **Cup products.** There are unique bi-additive pairings $H^r(G, M) \times H^s(G, N) \to H^{r+s}(G, M \otimes N)$ for $r, s \ge 0$,
  natural in $M$ and $N$, given in degree $0$ by $M^G \otimes N^G \to (M \otimes N)^G$, $m \otimes n \mapsto m \otimes n$, and compatible
  with connecting homomorphisms in the following sense. If $0 \to M' \to M \to M'' \to 0$ is exact and stays exact after
  tensoring with $N$, then $\delta(m'') \cup n = \delta(m'' \cup n)$; if $0 \to N' \to N \to N'' \to 0$ is exact and stays exact after
  tensoring with $M$, then $m \cup \delta(n'') = (-1)^r \delta(m \cup n'')$ for $m \in H^r(G, M)$. On inhomogeneous cochains,
  $(f \cup g)(g_1, \dots, g_{r+s}) = f(g_1, \dots, g_r) \otimes g_1 \cdots g_r\, g(g_{r+1}, \dots, g_{r+s})$. They are associative,
  graded commutative, $x \cup y = (-1)^{rs} y \cup x$ after identifying $M \otimes N$ with $N \otimes M$, and satisfy
  $\mathrm{Res}(x \cup y) = \mathrm{Res}(x) \cup \mathrm{Res}(y)$, $\mathrm{Cor}(x \cup \mathrm{Res}\, y) = \mathrm{Cor}(x) \cup y$ and
  $\mathrm{Inf}(x \cup y) = \mathrm{Inf}(x) \cup \mathrm{Inf}(y)$.
- **Tate cohomology.** When $G$ is finite, the cup products extend uniquely to pairings
  $\hat H^r(G, M) \times \hat H^s(G, N) \to \hat H^{r+s}(G, M \otimes N)$ for all $r, s \in \mathbb{Z}$, natural, given in degree $0$ by
  the map $\hat H^0(G, M) \otimes \hat H^0(G, N) \to \hat H^0(G, M \otimes N)$ induced by $m \otimes n \mapsto m \otimes n$, compatible with
  the connecting homomorphisms under the same exactness conditions, associative, graded commutative and compatible
  with restriction and corestriction. Inflation $\hat H^r(G/H, M^H) \to \hat H^r(G, M)$, for $H$ normal in $G$, is defined
  only for $r \ge 1$, where Tate and ordinary cohomology agree, so the compatibility with inflation is that of ordinary
  cohomology in those degrees. In degree $0$ the identity of $M^G$ does not induce a map $\hat H^0(G/H, M^H) \to \hat H^0(G, M)$:
  for $G$ cyclic of order $4$, $H$ its subgroup of order $2$ and $M = \mathbb{Z}$ with trivial action, these groups are
  $\mathbb{Z}/2\mathbb{Z}$ and $\mathbb{Z}/4\mathbb{Z}$, and the identity of $\mathbb{Z}$ does not map the norms $2\mathbb{Z}$ of $G/H$ into the norms $4\mathbb{Z}$ of $G$.

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
  §1, "Cup-products", pp. 72–74, Proposition 1.38 (existence and uniqueness, with conditions (a)–(d), including the
  exactness of the tensored sequences and the sign $(-1)^r$, and the cochain formula) and Proposition 1.39 (associativity,
  graded commutativity, and compatibility with restriction, corestriction and inflation), §3, p. 79, footnote 4 (Tate
  inflation is defined only in degrees $r \ge 1$), and §3, "Cup-products",
  p. 80 ("When the group G is finite, the cup-products extend in a unique way to all the cohomology groups, and have the
  same list of properties. See Weiss 1969, Chapter IV").
- E. Weiss, *Cohomology of groups*, Academic Press, 1969, Chapter IV, as cited by Milne.
