# Linear algebraic groups over local fields and their groups of rational points

This node is still to be broken down. It covers the definitions and basic topological facts about
reductive groups over local fields that the pages on representations of $p$-adic and real reductive
groups take as their setting.

- **Linear algebraic groups.** Linear algebraic groups over a field $k$ (smooth affine group schemes of
  finite type over $k$, or, for $k$ perfect, reduced Zariski-closed subgroups of some $\mathrm{GL}_N$ defined over
  $k$), their identity components, tori and $k$-split tori, unipotent radicals, and connected reductive groups:
  smooth connected affine groups whose unipotent radical over an algebraic closure is trivial. Smoothness is
  part of the definition: in characteristic $p$ the group scheme $\mu_p$ is affine, of finite type, connected
  and of multiplicative type, with no nontrivial smooth connected unipotent normal subgroup, but it is not
  smooth, hence not reductive; a closed subgroup scheme need not be reduced, unlike a Zariski-closed
  subgroup in the classical sense. A group is Zariski-connected when it is connected as an algebraic group;
  its group of real points need not be connected.
- **Topology of rational points.** For a local field $F$ and a linear algebraic group $\mathbf{G}$ over
  $F$, the topology induced on $\mathbf{G}(F)$ by a closed embedding into $\mathrm{GL}_N$ does not depend on
  the embedding, and makes $\mathbf{G}(F)$ a locally compact Hausdorff topological group. If $F$ is
  non-archimedean, $\mathbf{G}(F)$ is an $\ell$-group: the subgroups
  $\mathbf{G}(F) \cap (1 + \varpi^n \mathrm{M}_N(\mathcal{O}_F))$, $n \ge 1$, are compact open and form a
  basis of neighbourhoods of the identity. If $F = \mathbb{R}$, $\mathbf{G}(\mathbb{R})$ is a real Lie group
  with finitely many connected components.
- **Maximal compact subgroups.** For $\mathbf{G}$ connected reductive over $\mathbb{R}$, the group
  $\mathbf{G}(\mathbb{R})$ has maximal compact subgroups, and they are all conjugate. For a connected linear
  semisimple Lie group this is E. Cartan's theorem (Etingof, Theorem 5.13); the extension to
  $\mathbf{G}(\mathbb{R})$, which can be disconnected and has a centre, is a separate step, through the finiteness of
  its components and the theorem on the maximal compact subgroups of Lie groups with finitely many components.

## Expansion

A good expansion has definition pages for linear algebraic groups, connected reductive groups and split
tori, statement pages for the topology of rational points over a local field (the $\ell$-group property
in the non-archimedean case and the Lie group structure in the real case) and for the existence and
conjugacy of maximal compact subgroups of real points, each citing a pinned source with locators
besides those below.

It also writes out these steps of its own proof:

- the local compactness of $\mathrm{M}_N(F) \cong F^{N^2}$ for a local field $F$, and the closedness of the image of a closed embedding, for the topology of rational points.
- the passage from the identity component $\mathbf{G}(\mathbb{R})^0$ to $\mathbf{G}(\mathbb{R})$, which has finitely many components, for the extension to $\mathbf{G}(\mathbb{R})$.

## Depends on

- [Topological group](../../Topology/topological-groups/topological-group.md), for the topology of rational points
- [Geometrically reduced variety over a field](../../AlgebraicGeometry/schemes-and-morphisms/varieties-over-a-field/is-variety.md), for varieties over a field and their Zariski topology, for the definitions
- [Lie group](../../Geometry/differential-topology/lie-group.md), for real Lie groups, for the real case
- [Lie groups: the exponential map, closed subgroups and maximal compact subgroups](../lie-and-topological-representations/lie-groups-exponential-map-and-maximal-compact-subgroups.md), for their Lie algebras and closed subgroups, for the real case

## Proof depends on

- [Compactness of the completed ring of integers](../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/adeles-and-ideles/is-compact-adic-completion-integers.md), for the local compactness of the completions of number fields, whose rings of integers are compact open subrings
- [Lie groups: the exponential map, closed subgroups and maximal compact subgroups](../lie-and-topological-representations/lie-groups-exponential-map-and-maximal-compact-subgroups.md), for the closed subgroup theorem, in the real case; and for E. Cartan's conjugacy theorem and the Cartan decomposition, for the conjugacy of maximal compact subgroups in the connected linear semisimple case; and for the existence and conjugacy of maximal compact subgroups of Lie groups with finitely many components, which with the finiteness of the components of $\mathbf{G}(\mathbb{R})$ gives the extension to $\mathbf{G}(\mathbb{R})$
- [Finiteness of the connected components of real algebraic varieties and groups](connected-components-of-real-algebraic-groups.md), for the finiteness of the connected components of real algebraic sets and of $\mathbf{G}(\mathbb{R})$, in the real case

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §1.1 ($\ell$-groups) and §2.1 ("In a natural
  locally compact topology such groups are $\ell$-groups", for the groups of $F$-points of algebraic
  groups over a locally compact non-archimedean field).
- P. Etingof, "Representations of Lie groups", lecture notes, arXiv:2401.01446 (version 3): §5.3, the
  definition of a semisimple Lie group as the identity component of the real points of a semisimple
  algebraic group over $\mathbb{R}$, and Theorem 5.13 (E. Cartan: a maximal compact subgroup exists and is
  unique up to conjugation).
- W. Casselman, "Canonical extensions of Harish-Chandra modules to representations of G", Canad. J.
  Math. 41 (1989), 385–438, <https://doi.org/10.4153/CJM-1989-019-5>: introduction (the class of groups,
  real points of Zariski-connected reductive groups, with a maximal compact subgroup).
