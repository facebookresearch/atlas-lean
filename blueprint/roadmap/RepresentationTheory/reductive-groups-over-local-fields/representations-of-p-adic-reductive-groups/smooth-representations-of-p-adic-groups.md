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

**Distribution characters.** Fix a Haar measure $dg$ on $G$, let $H(G)$ be the space of locally
constant compactly supported functions on $G$, and for a smooth representation $(\pi, V)$ and
$f \in H(G)$ let $\pi(f)v = \int_G f(g)\pi(g)v \, dg$. If $\pi$ is admissible, every $\pi(f)$ has finite
rank, and the **distribution character** of $\pi$ is the linear form
$\mathrm{ch}_\pi(f) = \operatorname{trace} \pi(f)$ on $H(G)$. It is additive in short exact sequences of
admissible representations. The distribution characters of pairwise inequivalent irreducible
admissible representations are linearly independent, and two admissible representations of finite
length have the same irreducible composition factors, with multiplicities, if and only if they have
the same distribution character.

## Depends on

- [Linear algebraic groups over local fields and their groups of rational points](../linear-algebraic-groups-over-local-fields.md), for the groups $\mathbf{G}(F)$ as $\ell$-groups (the example in the first paragraph) and for connected reductive groups, the setting of Schur's lemma and central characters
- [ℓ-spaces, distributions and smooth representations of ℓ-groups](l-spaces-distributions-and-smooth-representations-of-l-groups.md), for $\ell$-groups and smooth and admissible representations, which the first paragraph and the first two items recall

## Proof depends on

- [Existence of an eigenvalue over an algebraically closed field](../../../LinearAlgebra/eigenvalues-and-canonical-forms/existence-of-eigenvalues/exists-eigenvalue.md), for Schur's lemma: a nonzero vector has an open stabilizer containing a compact open subgroup $K$, so $V^K \ne 0$; a $G$-endomorphism $T$ of an irreducible admissible $V$ preserves the finite-dimensional space $V^K$, so it has an eigenvalue $c$ there, and $\ker(T - c)$ is a nonzero subrepresentation, hence $V$ (Wedhorn, (2.1.16))
- [Trace splits along a surjective intertwining map](../../../LinearAlgebra/linear-maps-and-duality/trace-on-invariant-subspaces/trace-eq-trace-restrict-ker-add-of-surje.md), for the additivity of distribution characters: for $f$ bi-invariant under a compact open subgroup $K$, $\pi(f) = \pi(e_K)\pi(f)\pi(e_K)$ maps $V$ into $V^K$ and vanishes on $\ker \pi(e_K)$, so $\mathrm{ch}_\pi(f)$ is the trace on $V^K$; in an exact sequence $0 \to V' \to V \to V'' \to 0$, taking $K$-fixed vectors is exact (averaging a lift of a $K$-fixed vector over $K$ gives a $K$-fixed lift), and this page applies to the surjection $V^K \to V''^K$ (Casselman, the proof of Corollary 2.3.3)
- [Hecke-algebra corners of smooth representations and independence of their characters](hecke-algebra-corners-and-character-independence.md), for the linear independence of distribution characters: for finitely many pairwise inequivalent irreducible admissible $V_i$, a compact open $K$ with every $V_i^K \ne 0$ makes the $V_i^K$ pairwise inequivalent simple $\mathcal{H}(G, K)$-modules, whose traces are linearly independent (Casselman, Proposition 2.3.1, citing Jacquet–Langlands, Lemma 7.1)
- [Locally constant compactly supported functions have uniform stabilizers](../../../Topology/topological-groups/exists-is-open-one-mem-forall-mul-eq-of.md), for the finite rank of $\pi(f)$ when $\pi$ is admissible: $f$ is invariant under left and right translation by an open neighbourhood of $1$, which contains a compact open subgroup $K$ as $G$ is an $\ell$-group, so $\pi(f)$ maps $V$ into $V^K$
- [Generation of the special linear group by elementary transvections](../../../GroupTheory/linear-groups/generation-of-special-linear-groups-by-transvections.md), for the characters of $\mathrm{GL}_n(F)$: the kernel of a character is open, so it contains $1 + a e_{ij}$ for $i < j$ and $a$ small, hence, conjugating by diagonal matrices, the whole upper unitriangular group, and the character factors through $\det$ (Wedhorn, the proof of (2.1.18))

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
  §2.1 (smooth, admissible, irreducible and finitely generated representations), §2.3
  (distribution characters, Proposition 2.3.1 on linear independence, Corollaries 2.3.2 and 2.3.3,
  with additivity in exact sequences in the proof of 2.3.3).
