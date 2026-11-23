# Continuous extension of (g, K)-maps into smooth Fréchet representations

This node is still to be broken down. Let $G$ be the group of real points of a Zariski-connected
reductive algebraic group over $\mathbb{R}$ with maximal compact subgroup $K$, as in the
[Casselman–Wallach globalization theorem](casselman-wallach-globalization.md). It covers the
following extension statement, which is stronger than item 1 of that page because only the source
is assumed to lie in the Casselman–Wallach category.

- **Statement.** Let $V$ be a [Harish-Chandra module](harish-chandra-modules.md), $V^\infty$ its
  Casselman–Wallach globalization, and $(\pi, E)$ any smooth Fréchet representation of $G$ of
  moderate growth. Every $(\mathfrak{g}, K)$-map $T_0 \colon V \to E$, with values in the smooth
  $K$-finite vectors of $E$, extends uniquely to a continuous $G$-map $T \colon V^\infty \to E$, and
  $T$ has closed image. When $V$ is irreducible and $T_0 \ne 0$, $T$ is a topological isomorphism
  onto its image.
- **The bridge to the globalization theorem.** The image $W = T_0(V)$ is a quotient of $V$, hence
  a Harish-Chandra module. Its closure $\overline{W}$ in $E$ is a smooth Fréchet representation of
  moderate growth whose $K$-finite vectors are $W$: each $K$-isotypic projection of $E$ is
  continuous and $W$ has finite-dimensional isotypic components, and the $G$-stability of
  $\overline{W}$ comes from the analyticity of the matrix coefficients of $K$-finite vectors. So
  $\overline{W}$ is a smooth Fréchet globalization of $W$, and the universal property of the
  minimal globalization of $W$, which by the Casselman–Wallach theorem is its only one, gives a
  continuous $G$-map $W^\infty \to \overline{W}$ extending the identity of $W$. Composed with the
  map $V^\infty \to W^\infty$ that the globalization functor attaches to $V \to W$, it extends
  $T_0$. Its image is closed because the globalization functor is exact. Uniqueness holds because
  $V$ is dense in $V^\infty$.

A good expansion has a statement page for the extension theorem, and pages for the steps of the
bridge: the closure of a Harish-Chandra module of smooth $K$-finite vectors as a globalization,
the minimal globalization with its universal property, and the quotient compatibility of
globalizations. Each page cites the sources below with locators. Casselman's Corollary 10.5 is
printed with the hypothesis on the target instead of the source, so it cannot be cited for the
statement as it stands; Casselman's justification ("the quotient of U by the closure of the kernel
is a Harish-Chandra representation") is the argument above.

## Depends on

- [Casselman–Wallach globalization theorem](casselman-wallach-globalization.md), for the globalization $V^\infty$ and smooth Fréchet representations of moderate growth
- [Harish-Chandra modules](harish-chandra-modules.md), for Harish-Chandra modules and $(\mathfrak{g}, K)$-maps

## Sources

- J. Bernstein and B. Krötz, "Smooth Fréchet globalizations of Harish-Chandra modules", Israel J.
  Math. 199 (2014), 45–111, arXiv:0812.1684 (version 3): §1 (the Casselman–Wallach theorem as an
  equivalence of categories with continuous $G$-maps as morphisms, and $V^\infty = \pi(\mathcal{S}(G))V$),
  §6.1 (minimal globalizations: "if $(\pi, E)$ is an SF-globalization of V, then there exists a
  continuous G-equivariant map $V^\infty \to E$ which extends the identity morphism"), Lemma 6.1
  (analyticity of the matrix coefficients $\xi(\pi(g)v)$, $\xi \in \tilde V$, for Banach
  globalizations), Lemma 6.2 ($U^\infty = V^\infty/\overline{W}$ for $U = V/W$). This universal
  property assumes that $E$ is already a globalization of $V$; the bridge above reduces the general
  target to that case.
- W. Casselman, "Canonical extensions of Harish-Chandra modules to representations of G", Canad. J.
  Math. 41 (1989), 385–438, <https://doi.org/10.4153/CJM-1989-019-5>: Corollary 10.5 and the
  sentence after it.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the statement above for irreducible unitary representations of the groups $\mathrm{U}(p, q)$
  as `GlobalTheory.Published.CasselmanWallach` and, without the closed image,
  as `GlobalTheory.Published.CasselmanWallachLift`.
