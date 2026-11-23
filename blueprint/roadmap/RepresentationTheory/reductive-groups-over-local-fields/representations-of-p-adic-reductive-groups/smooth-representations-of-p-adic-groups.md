# Smooth and admissible representations of p-adic groups

An $\ell$-group is a Hausdorff topological group in which every neighbourhood of the identity
contains a compact open subgroup; for a non-archimedean local field $F$ and an algebraic group
$\mathbf{G}$ over $F$, the group $\mathbf{G}(F)$ with its natural topology is an $\ell$-group. Let
$G$ be an $\ell$-group. All representations are on complex vector spaces, with no topology.

- A representation $(\pi, V)$ of $G$ is **smooth** if the stabilizer of every vector of $V$ is
  open in $G$. Smooth representations and $G$-linear maps form an abelian category
  $\mathrm{Alg}\, G$; subrepresentations, quotients and subquotients of smooth representations are
  smooth. A smooth representation is **irreducible** if $V \ne 0$ and $0$ and $V$ are its only
  $G$-stable subspaces, and it has **finite length** if it has a finite composition series.
- A smooth representation is **admissible** if the space $V^K$ of $K$-fixed vectors is
  finite-dimensional for every open subgroup $K$ of $G$.
- The **contragredient** $(\tilde\pi, \tilde V)$ of a smooth representation is the
  representation $\langle \tilde\pi(g)\lambda, v\rangle = \langle \lambda, \pi(g^{-1})v\rangle$ on
  the space $\tilde V$ of linear forms on $V$ whose stabilizer is open. If $\pi$ is admissible,
  then so is $\tilde\pi$, the canonical map $V \to \tilde{\tilde V}$ is an isomorphism, and $\pi$
  is irreducible if and only if $\tilde\pi$ is. For $v \in V$ and $\lambda \in \tilde V$ the
  function $c_{v,\lambda}(g) = \langle \lambda, \pi(g)v \rangle$ is a **matrix coefficient** of
  $\pi$.
- A **character** of $G$ is a locally constant homomorphism $\theta \colon G \to \mathbb{C}^\times$,
  and $\theta\pi$ is the representation $g \mapsto \theta(g)\pi(g)$ on $V$; it is smooth,
  admissible or irreducible exactly when $\pi$ is. For $G = \mathrm{GL}_n(F)$ every character is
  $\chi \circ \det$ for a character $\chi$ of $F^\times$, and one writes $\pi\chi$ for
  $(\chi \circ \det)\pi$.
- A smooth representation is **unitarizable** if $V$ carries a positive definite $G$-invariant
  Hermitian form.

Let now $G = \mathbf{G}(F)$ for a connected reductive group $\mathbf{G}$ over $F$, with centre
$Z$. **Schur's lemma**: every $G$-endomorphism of an irreducible admissible representation
$(\pi, V)$ is a scalar. Hence $Z$ acts on $V$ through a character $\omega_\pi$, the **central
character** of $\pi$: $\pi(z) = \omega_\pi(z)\,\mathrm{id}_V$ for $z \in Z$; for
$G = \mathrm{GL}_n(F)$, $Z = F^\times$ and $\omega_\pi$ is a character of $F^\times$.

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §1.1 ($\ell$-groups, with the example of
  $p$-adic Lie groups), §1.2 (algebraic, that is smooth, representations, the category
  $\mathrm{Alg}\, G$, subquotients and length), §1.3 (admissible representations), §1.4
  (contragredient: "If $\pi$ is admissible, so is $\tilde\pi$, and $\tilde{\tilde\pi} = \pi$"),
  §1.5 (characters and twists), §2.1 (groups of $F$-points are $\ell$-groups).
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): (2.1.3) (smooth and admissible representations), (2.1.16)
  (Schur's lemma, proved there for admissible representations), (2.1.18) and (2.1.21) (characters
  of $\mathrm{GL}_n(K)$ and twists), (2.1.19) (central characters), (2.1.22) (1)–(2)
  (contragredient), (2.2.5) (matrix coefficients).
- M. Tadić, "Classification of unitary representations in irreducible representations of general
  linear group (non-Archimedean case)", Ann. Sci. École Norm. Sup. (4) 19 (1986), 335–382,
  <http://www.numdam.org/item?id=ASENS_1986_4_19_3_335_0>: §1.2 (unitarizable representations).
- W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, notes, draft of 1 May 1995, <https://personal.math.ubc.ca/~cass/research/pdf/p-adic-book.pdf>:
  §2.1 (smooth, admissible, irreducible and finitely generated representations).
