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
- **Proof.** It has three steps.
  1. *Existence and uniqueness of $T$.* A smooth Fréchet representation of moderate growth is a
     smooth F-representation (an SF-representation) in the sense of Bernstein and Krötz, so the
     action of $C_c^\infty(G)$ on $E$ extends to a continuous action of the Schwartz algebra
     $\mathcal{S}(G)$, and $E$ is a smooth $\mathcal{S}(G)$-representation. By Bernstein and
     Krötz's lifting theorem, restriction to $V$ is a linear isomorphism
     $\mathrm{Hom}_G(V^\infty, E) \to \mathrm{Hom}_{(\mathfrak{g}, K)}(V, E_{K\text{-fin}})$ from the
     continuous $G$-maps onto the $(\mathfrak{g}, K)$-maps into the $K$-finite vectors. So $T_0$
     extends to exactly one continuous $G$-map $T$. In their proof, $T(\Lambda(f)w) = \Pi(f)T_0(w)$
     for $f \in \mathcal{S}(G)$ and $w \in V$, where $\Lambda$ and $\Pi$ are the actions of
     $\mathcal{S}(G)$ on $V^\infty$ and on $E$. This is well defined because two distributions on
     $G$ that are $Z(\mathfrak{g})$-finite and $K \times K$-finite are analytic functions determined
     by their derivatives on $K$, and $T$ is continuous because $V^\infty$ is a quotient of
     $\mathcal{S}(G)^k$.
  2. *Closed image.* The $K$-finite vectors of $T(V^\infty)$ form $T_0(V)$. If $T(v)$ is $K$-finite,
     with $K$-types in a finite set $S$, the $K$-isotypic projection $P_S$, which is continuous and
     commutes with $T$, gives $T(v) = P_S T(v) = T(P_S v)$, and $P_S v$ is a $K$-finite vector of
     $V^\infty$, that is, an element of $V$. So the underlying $(\mathfrak{g}, K)$-module of the image
     is a quotient of $V$, a Harish-Chandra module of finite length. By Casselman's closed-range
     theorem, a continuous $G$-map between smooth representations of moderate growth whose image has
     such an underlying module has closed range.
  3. *Irreducible source.* If $V$ is irreducible and $T_0 \ne 0$, then $T_0$ is injective. The
     kernel of $T$ is a closed $G$-stable subspace of $V^\infty$ whose $K$-finite vectors lie in
     $\ker T_0 = 0$, so it is zero, by the correspondence between closed $G$-stable subspaces and
     $(\mathfrak{g}, K)$-submodules. Then $T$ is a continuous bijection from $V^\infty$ onto the closed,
     hence Fréchet, subspace $T(V^\infty)$ of $E$, and a topological isomorphism by the open mapping
     theorem.

A good expansion has a statement page for the extension theorem and separate pages for its three
proof inputs: the continuous action of $\mathcal{S}(G)$ on SF-representations (Bernstein–Krötz,
Proposition 2.20), the lifting isomorphism (Bernstein–Krötz, Proposition 11.2) and Casselman's
closed-range theorem (Casselman 1989, p. 386). The notions they use, the Schwartz algebra
$\mathcal{S}(G)$, F- and SF-representations and $\mathcal{S}(G)$-representations, get definition
pages, which are not proof inputs. The isotypic projections and the correspondence between closed
invariant subspaces and submodules are on the pages linked below; the open mapping theorem for
Fréchet spaces is standard. Each page cites the sources below with locators. Casselman's Corollary
10.5 is printed with its hypothesis on the target, not on the source, and is not used.

## Depends on

- [Casselman–Wallach globalization theorem](casselman-wallach-globalization.md), for the globalization $V^\infty$ and smooth Fréchet representations of moderate growth
- [Harish-Chandra modules](harish-chandra-modules.md), for Harish-Chandra modules and $(\mathfrak{g}, K)$-maps

## Proof depends on

- [Casselman–Wallach globalization theorem](casselman-wallach-globalization.md), for the realization of $V^\infty$ as a quotient of $\mathcal{S}(G)^k$ by a closed submodule, used in the lifting isomorphism
- [Harish-Chandra modules](harish-chandra-modules.md), for the finite length of the quotients of Harish-Chandra modules (item 1) and the correspondence between the closed $G$-stable subspaces of an admissible representation and the $(\mathfrak{g}, K)$-submodules of its $K$-finite vectors (item 2), used for the closed image and the injectivity of $T$

## Sources

- J. Bernstein and B. Krötz, "Smooth Fréchet globalizations of Harish-Chandra modules", Israel J.
  Math. 199 (2014), 45–111, arXiv:0812.1684 (version 3): §2.1.2 and Lemma 2.1 (for real reductive
  groups the algebraic norm defines the scale structure), Definition 2.6 and Lemma 2.10
  (F-representations are the Fréchet representations of moderate growth; SF-representations are the
  smooth ones), p. 12 (every F-representation integrates to a continuous algebra representation of
  $\mathcal{R}(G) \supset \mathcal{S}(G)$), Proposition 2.20 (pp. 12–13: SF-representations are
  equivalent to the non-degenerate continuous algebra representations of $\mathcal{S}(G)$ on Fréchet
  spaces), and §11.1 with Proposition 11.2 (pp. 46–47: "for any smooth $\mathcal{S}(G)$-representation
  $(\pi, E)$ of G the linear map $\mathrm{Hom}_G(V^\infty, E) \to \mathrm{Hom}_{(\mathfrak{g}, K)}(V, E_{K-\mathrm{fin}})$,
  $T^\infty \mapsto T^\infty|_V$ is a linear isomorphism", proved through $Z(\mathfrak{g})$- and
  $K \times K$-finite distributions and the realization $V^\infty = \mathcal{S}(G)^k/\mathcal{S}(G)_v$
  of §6.1).
- W. Casselman, "Canonical extensions of Harish-Chandra modules to representations of G", Canad. J.
  Math. 41 (1989), 385–438, <https://doi.org/10.4153/CJM-1989-019-5>: p. 386 ("if U and V are the
  spaces of smooth representations of G of moderate growth, then any continuous G-covariant map from
  U to V whose image has the property that its underlying $(\mathfrak{g}, K)$-subspace is a
  Harish-Chandra module of finite length has closed range"), for step 2, and Proposition 2.2 (d)
  (closed $G$-stable subspaces and $(\mathfrak{g}, K)$-submodules, with the continuity of the
  $K$-isotypic projections in the proof of (b)), for steps 2 and 3. Corollary 10.5 is printed with
  its hypothesis on the target.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the statement above for irreducible unitary representations of the groups $\mathrm{U}(p, q)$
  as `GlobalTheory.Published.CasselmanWallach` and, without the closed image,
  as `GlobalTheory.Published.CasselmanWallachLift`.
