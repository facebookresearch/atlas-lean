# Unitary representations of locally compact groups and representations of compact groups

This node is still to be broken down. It covers the definitions of unitary representations and regular
representations, and the structure of the representations of compact groups, that the pages on Lie groups,
on Heisenberg groups and on automorphic forms use. Groups are locally compact Hausdorff
[topological groups](../../Topology/topological-groups/topological-group.md) with a left [Haar measure](../../MeasureTheory/haar-measure/is-haar-measure.md) $dg$.

- **Unitary representations.** A unitary representation of $G$ on a complex Hilbert space $V$ is a homomorphism
  $\pi$ from $G$ to the group of unitary operators on $V$ such that $g \mapsto \pi(g)v$ is continuous for every
  $v \in V$. The right regular representation $(R(h)f)(g) = f(gh)$ of $G$ on $L^2(G, dg)$ is unitary when $G$ is
  unimodular, and the left regular representation $(L(h)f)(g) = f(h^{-1}g)$ is always unitary.
- **Compact groups: finite dimensionality and characters.** Let $K$ be a compact group, with countable basis,
  and $dk$ its Haar measure of total mass $1$. Every irreducible unitary representation $\tau$ of $K$ is finite
  dimensional; its character is $\chi_\tau(k) = \operatorname{tr} \tau(k)$.
- **Schur orthogonality.** For irreducible unitary representations $\tau, \tau'$ of $K$, with orthonormal bases
  and matrix coefficients $\tau_{ij}$, $\tau'_{kl}$, $\int_K \tau_{ij}(k) \overline{\tau'_{kl}(k)} \, dk = 0$ if
  $\tau \not\cong \tau'$, and $= \delta_{ik} \delta_{jl} / \dim \tau$ if $\tau = \tau'$. The characters of the
  irreducible representations form an orthonormal basis of the conjugation-invariant functions in $L^2(K)$.
- **Isotypic decomposition.** Every unitary representation $\sigma$ of $K$ on a Hilbert space $V$ (not
  necessarily irreducible nor finite dimensional) is the completed orthogonal direct sum of its isotypic
  components $V^\tau$, $\tau$ running over the isomorphism classes of irreducible unitary representations of $K$.
- **Compact abelian groups.** Let $K$ be a compact abelian group, not necessarily with a countable basis, and $dk$
  its Haar measure of total mass $1$. Its irreducible unitary representations are the continuous characters
  $\chi \colon K \to \mathbb{C}^1$, and they form an orthonormal basis of $L^2(K)$. Every unitary representation $\sigma$ of
  $K$ on a Hilbert space $V$ is the completed orthogonal direct sum of the character spaces
  $V^\chi = \{v \in V : \sigma(k)v = \chi(k)v \text{ for all } k \in K\}$, of arbitrary dimension, and the orthogonal
  projection onto $V^\chi$ is $v \mapsto \int_K \overline{\chi(k)} \, \sigma(k)v \, dk$.

## Expansion

A good expansion has definition pages for unitary representations and the regular representations, and
statement pages for the finite dimensionality of the irreducible representations of compact groups, the
Schur orthogonality relations and the completeness of characters, and the isotypic decomposition of an
arbitrary unitary representation of a compact group, each citing the sources below with locators, and a statement
page for the compact abelian case without countability. For $K$ abelian the projection formula is checked directly:
$\sigma(k')$ applied to $\int_K \overline{\chi(k)} \sigma(k)v \, dk$ gives $\chi(k')$ times it, by the invariance of $dk$, and
it is the identity on $V^\chi$ and zero on $V^{\chi'}$ for $\chi' \ne \chi$ by orthogonality of characters. The
characters separate the points of $K$: finite-dimensional unitary representations do, and such a representation of an
abelian group is a sum of characters. By the Stone–Weierstrass theorem they therefore span a dense subalgebra of
$C(K)$, hence of $L^2(K)$. So if $v$ is orthogonal to every $V^\chi$, each continuous function $k \mapsto \langle \sigma(k)v, w \rangle$
is orthogonal to every character, hence zero, and $v = 0$. In the finite-dimensional case, the semisimplicity of
real representations of compact groups gives complex invariant complements through the invariant Hermitian inner
product obtained by averaging.

## Depends on

- [Topological group](../../Topology/topological-groups/topological-group.md), for the setting
- [Haar measure](../../MeasureTheory/haar-measure/is-haar-measure.md), for $L^2(G)$ and the regular representations

## Proof depends on

- [Existence of Haar measure](../../MeasureTheory/haar-measure/existence-and-uniqueness-of-haar-measure/is-haar-measure-haar-measure.md), for the normalised Haar measure of a compact group
- [Peter–Weyl theorem: unitary representations separate points](representations-of-compact-groups/peter-weyl-point-separation.md), for the completeness of the
  matrix coefficients, and for the separation of points by characters of a compact abelian group
- [Stone–Weierstrass theorem for star subalgebras](../../Topology/function-spaces/stone-weierstrass-star-subalgebra.md), for the density of the algebra spanned by
  the matrix coefficients, and by the characters in the abelian case, in $C(K)$
- [Representations of compact groups are semisimple](representations-of-compact-groups/compact-group-semisimple.md), for the finite-dimensional case, where it
  is a statement about real representations and the complex case uses invariant Hermitian complements

## Sources

- P. Garrett, "Unitary representations of topological groups", notes, 3 August 2014,
  <https://www-users.cse.umn.edu/~garrett/m/repns/notes_2014-15/06a_unitary_of_top.pdf>: §1 (unitary representations, with the strong continuity), §3 (isotypic components), §5, Proposition
  [5.0.1] (the regular representations), §24, Theorem [24.0.1], §25, Corollary [25.0.1] (compact $Z \backslash G$:
  irreducibles are finite dimensional), §29, Definition [29.0.1] and Theorem [29.0.4] (characters, an orthogonal
  basis of the central functions), and §30, Theorem [30.0.1] (an arbitrary unitary representation is the completed
  orthogonal sum of its isotypic components), for groups that are locally compact, Hausdorff and countably based.
- P. Etingof, "Lie groups and Lie algebras", lecture notes, arXiv:2201.09397 (version 5), <https://arxiv.org/abs/2201.09397>: §35.2, Theorem 35.4 (orthogonality of matrix coefficients), §35.5, Corollary 35.9 (characters, an
  orthonormal basis of the class functions), and §37, Theorems 37.1 and 37.5 (Haar measure and the Peter–Weyl
  theorem for compact topological groups with a countable base).
- A. Prasad, "An easy proof of the Stone–von Neumann–Mackey theorem", arXiv:0912.0574 (2009): §2 (locally compact
  Hausdorff abelian groups, with no countability assumption) and §4.2, p. 4 (the decomposition of a unitary
  representation of a compact abelian group into character spaces, by the Peter–Weyl theorem).
