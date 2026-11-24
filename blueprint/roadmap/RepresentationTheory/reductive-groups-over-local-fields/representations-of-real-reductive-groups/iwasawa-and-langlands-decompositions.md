# Iwasawa and Langlands decompositions of real reductive groups

This node is still to be broken down. It covers the structure of the real points of reductive groups that
reduction theory, the principal series and the automorphic pages use. Let $\mathbf{G}$ be a connected
reductive group over $\mathbb{R}$, $G = \mathbf{G}(\mathbb{R})$, and $K$ a maximal compact subgroup of $G$, with
Cartan involution $\theta$ and Cartan decomposition $\mathfrak{g} = \mathfrak{k} \oplus \mathfrak{p}$.

- **Iwasawa decomposition.** For a maximal abelian subspace $\mathfrak{a} \subseteq \mathfrak{p}$, an ordering of the
  roots of $\mathfrak{a}$ in $\mathfrak{g}$ and $\mathfrak{n}$ the sum of the positive root spaces, with $A = \exp \mathfrak{a}$ and
  $N = \exp \mathfrak{n}$, the multiplication map $K \times A \times N \to G$ is a homeomorphism (a diffeomorphism).
  $AN$ is the identity component of the real points of a maximal $\mathbb{R}$-trigonalizable subgroup, and for
  every parabolic $\mathbb{R}$-subgroup $\mathbf{P}$ of $\mathbf{G}$, $G = \mathbf{P}(\mathbb{R}) K$.
- **Langlands decompositions.** Let $P_{\min} = MAN$ be the minimal parabolic subgroup containing $AN$, with
  $M = Z_K(\mathfrak{a})$. Each parabolic subgroup $P \supseteq P_{\min}$ corresponds to a subset $F$ of the simple roots
  of $\mathfrak{a}$ in $\mathfrak{n}$ and has a Langlands decomposition $P = N_P A_P M_P$, with $N_P$ its unipotent radical,
  $A_P = \{a \in A : a^\alpha = 1 \text{ for all } \alpha \in F\}$, $M_P A_P = Z_G(A_P)$ and $K \cap P = K \cap M_P$;
  every parabolic subgroup of $G$ is conjugate to one of these.
- **Cartan subalgebras.** Every Cartan subalgebra of $\mathfrak{g}$ is conjugate under $G$ to a $\theta$-stable one
  $\mathfrak{h} = (\mathfrak{h} \cap \mathfrak{k}) \oplus (\mathfrak{h} \cap \mathfrak{p})$; any two maximally split, and any two
  maximally compact, $\theta$-stable Cartan subalgebras are conjugate under $K$. A Cartan subgroup is the
  centralizer in $G$ of a Cartan subalgebra.

## Expansion

A good expansion has statement pages for the Iwasawa decomposition, for $G = \mathbf{P}(\mathbb{R})K$, for the
Langlands decompositions of real parabolic subgroups and for the conjugacy of Cartan subalgebras, each
citing the sources below with locators. $G = \mathbf{P}(\mathbb{R})K$ follows for every maximal compact $K$ and every
parabolic $\mathbf{P}$ from the case of a minimal parabolic $\mathbf{P}_0 \supseteq AN$, since $\mathbf{P}$ contains a
$G$-conjugate of $\mathbf{P}_0$ and all maximal compact subgroups are conjugate. Borel and Tits and Etingof treat
semisimple groups; the reductive case reduces to it through the identity component of the centre, the derived
group and the finitely many connected components of $G$. The decompositions extend to a
connected semisimple Lie group with finite centre that is not linear: it is a finite central cover of the
identity component of the real points of its adjoint group, and the decompositions lift, the kernel lying in
$K$ and in $M$.

## Depends on

- [Linear algebraic groups over local fields and their groups of rational points](../linear-algebraic-groups-over-local-fields.md), for the setting
- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for parabolic
  $\mathbb{R}$-subgroups and their Levi factors
- [Lie groups: the exponential map, closed subgroups and maximal compact subgroups](../../lie-and-topological-representations/lie-groups-exponential-map-and-maximal-compact-subgroups.md), for $K$ and the
  Cartan decomposition
- [Relative roots, root space decompositions and root subgroups of reductive groups](../../../GroupTheory/linear-groups/relative-root-systems-and-root-subgroups.md), for the restricted roots of $\mathfrak{a}$ in $\mathfrak{g}$ and their root spaces, the relative roots of the maximal $\mathbb{R}$-split torus whose real points contain $A$

## Proof depends on

- [Lie groups: the exponential map, closed subgroups and maximal compact subgroups](../../lie-and-topological-representations/lie-groups-exponential-map-and-maximal-compact-subgroups.md), for the conjugacy
  of maximal compact subgroups, including those of Lie groups with finitely many components
- [Finiteness of the connected components of real algebraic varieties and groups](../connected-components-of-real-algebraic-groups.md),
  for the components of $G$ in the reductive case

## Sources

- A. Borel and J. Tits, "Groupes réductifs", Publ. Math. IHÉS 27 (1965), 55–150,
  <http://www.numdam.org/item?id=PMIHES_1965__27__55_0>: 14.7, pp. 147–148 (for $G$ semisimple over $\mathbb{R}$, the Cartan and Iwasawa decompositions,
  $(k, a, n) \mapsto kan$ a homeomorphism of $K \times A \times N$ onto $G_{\mathbb{R}}$, and $A \cdot N$ the identity component of
  the real points of a maximal $\mathbb{R}$-trigonalizable subgroup).
- P. Etingof, "Lie groups and Lie algebras", lecture notes, arXiv:2201.09397 (version 5), <https://arxiv.org/abs/2201.09397>: §44.6, Theorem 44.20 (θ-stable Cartan subalgebras of real semisimple Lie algebras: every Cartan
  subalgebra is conjugate to a θ-stable one, and the conjugacy of the maximally split and of the maximally compact
  ones), and §51, Theorem 51.14 and Exercise 51.15 (the Iwasawa decomposition and the minimal parabolic subalgebra
  $\mathfrak{m} \oplus \mathfrak{a} \oplus \mathfrak{n}$).
- J. Bernstein and B. Krötz, "Smooth Fréchet globalizations of Harish-Chandra modules", Israel J. Math. 199 (2014),
  45–111, arXiv:0812.1684 (version 3): §9.3 (a parabolic subgroup $P \supseteq P_{\min}$ with Langlands decomposition
  $P = N_P A_P M_P$, $M_P A_P = Z_G(A_P)$, the parametrization by subsets $F$ of the simple roots with
  $A_F = \{a \in A \mid a^\alpha = 1 \ (\alpha \in F)\}$, and $K_P = K \cap M_P$).
- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §4, p. 24 ($G(\mathbb{A}) = P(\mathbb{A})K = N_P(\mathbb{A}) M_P(\mathbb{A}) K$ for a suitable maximal compact $K$,
  and the decomposition of $M_P(\mathbb{A})$, citing J. Tits, "Reductive groups over local fields", (3.3.2) and (3.9)).
