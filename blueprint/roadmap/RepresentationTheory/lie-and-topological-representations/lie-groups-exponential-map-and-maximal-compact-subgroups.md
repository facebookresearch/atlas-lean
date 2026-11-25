# Lie groups: the exponential map, closed subgroups and maximal compact subgroups

This node is still to be broken down. It covers the structure of real Lie groups that the pages on
representations of Lie groups and of real reductive groups use. Let $G$ be a real
[Lie group](../../Geometry/differential-topology/lie-group.md), finite-dimensional and smooth, with Lie algebra $\mathfrak{g} = T_1 G$.

- **Exponential map.** For $X \in \mathfrak{g}$ there is a unique homomorphism $t \mapsto \exp(tX)$ from
  $\mathbb{R}$ to $G$ with derivative $X$ at $0$. The map $\exp \colon \mathfrak{g} \to G$ is smooth, restricts
  to a diffeomorphism from a neighbourhood of $0$ onto a neighbourhood of $1$, and has derivative the identity
  at $0$; $g \exp(X) g^{-1} = \exp(\mathrm{Ad}(g)X)$, and the flow of the left-invariant vector field defined by
  $X$ is $g \mapsto g \exp(tX)$.
- **Coordinates of the second kind.** For a basis $X_1, \dots, X_d$ of $\mathfrak{g}$, the map
  $(t_1, \dots, t_d) \mapsto \exp(t_1 X_1) \cdots \exp(t_d X_d)$ restricts to a diffeomorphism from a
  neighbourhood of $0$ in $\mathbb{R}^d$ onto a neighbourhood of $1$ in $G$.
- **Closed subgroups.** Every closed subgroup of $G$ is a closed embedded submanifold and a Lie group for the
  induced structure.
- **Maximal compact subgroups.** If $G$ is connected, it has maximal compact subgroups, every compact subgroup
  is contained in one of them, they are connected, any two are conjugate by an inner automorphism, and $G$ is
  homeomorphic to $K \times \mathbb{R}^s$ for a maximal compact subgroup $K$ (E. Cartan, Iwasawa, Malcev).
- **Lie groups with finitely many components.** If $G$ has finitely many connected components, it has maximal compact
  subgroups, any two are conjugate by an inner automorphism, and $G$ is homeomorphic to $K \times \mathbb{R}^s$ for a maximal
  compact subgroup $K$, which therefore meets every connected component of $G$.
- **Real semisimple groups** (E. Cartan). Let $G$ be a real form of a connected complex semisimple group, with
  Cartan decomposition $\mathfrak{g} = \mathfrak{k} \oplus \mathfrak{p}$ and $K$ the compact subgroup with Lie algebra
  $\mathfrak{k}$ acting unitarily on $\mathfrak{g}$. Every compact subgroup of $G$ is conjugate to a subgroup of $K$,
  and all maximal compact subgroups of $G$ are conjugate to $K$. For the adjoint group, with
  $A = \exp(\mathfrak{a})$ for a maximal abelian subspace $\mathfrak{a} \subseteq \mathfrak{p}$, every element is a product
  $k_1 a k_2$ with $k_1, k_2 \in K$ and $a \in A$ (the Cartan decomposition $G = KAK$).

## Expansion

A good expansion has statement pages for the exponential map and the flows of invariant vector fields, for
the coordinates of the second kind, for the closed subgroup theorem, for the existence and conjugacy of
maximal compact subgroups of connected Lie groups and of Lie groups with finitely many components, and for
E. Cartan's conjugacy theorem and the Cartan decomposition of real semisimple groups, each citing the sources below with locators. Etingof states the
Cartan decomposition for the adjoint group and notes (Remark 44.14) its extension to reductive groups. The coordinates
of the second kind follow from the inverse function theorem: the differential at $0$ of the product map
sends the $i$-th coordinate vector to $X_i$, since $\exp(t_i X_i)$ has derivative $X_i$ at $t_i = 0$.

## Depends on

- [Lie group](../../Geometry/differential-topology/lie-group.md), for the setting
- [Topological group](../../Topology/topological-groups/topological-group.md), for compact subgroups and their conjugacy

## Proof depends on

- [Surjective differential gives a submersion between finite-dimensional manifolds](../../Geometry/differential-topology/submersions/submersion-at-of-surjective-mfderiv.md), for the inverse function theorem behind the coordinates of the second kind: in equal dimensions the normal form of a submersion is a local diffeomorphism

## Sources

- P. Etingof, "Lie groups and Lie algebras", lecture notes, arXiv:2201.09397 (version 5), <https://arxiv.org/abs/2201.09397>: Definition 2.1 (Lie groups), §3.3, Theorem 3.13 (closed subgroups),
  §7.1, Definition 7.2, Proposition 7.3 and Theorem 7.5 (the exponential map, the flows of invariant vector
  fields and $g \exp(x) g^{-1} = \exp(\mathrm{Ad}_g x)$), §43.2 (the polar decomposition and the compact
  subgroup $K^c$), §44.4, Theorem 44.13 and Remark 44.14 (the Cartan decomposition), and
  §44.5, Theorem 44.16 (E. Cartan: a compact subgroup of a real form of a connected semisimple complex group is
  conjugate to a subgroup of $K$, and all maximal compact subgroups are conjugate).
- A. Borel, "Sous-groupes compacts maximaux des groupes de Lie", Séminaire Bourbaki, exp. no. 33
  (December 1950), 271–279, <http://www.numdam.org/item?id=SB_1948-1951__1__271_0>: §1, Théorème, p. 271
  (for a connected Lie group: existence of maximal compact subgroups containing every compact subgroup, their
  connectedness and conjugacy, and $G \cong K \times \mathbb{R}^s$; the existence of the decomposition is due to
  Iwasawa, the rest to E. Cartan for semisimple and simply connected groups and to Iwasawa and Malcev in general).
- A. Borel, *Semisimple groups and Riemannian symmetric spaces*, Texts and Readings in Mathematics 16, Hindustan Book
  Agency, 1998, Chapter VII, "Maximal compact subgroups of Lie groups", §1 (for a Lie group with finitely many connected
  components: existence of maximal compact subgroups, their conjugacy by inner automorphisms, and the homeomorphism with
  the product of one of them by a euclidean space) and §2 (its proof, through a theorem of Iwasawa on extensions of
  vector groups by compact groups).
