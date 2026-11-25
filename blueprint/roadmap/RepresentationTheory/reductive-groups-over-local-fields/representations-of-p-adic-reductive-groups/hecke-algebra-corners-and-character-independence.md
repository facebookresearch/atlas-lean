# Hecke-algebra corners of smooth representations and independence of their characters

This node is still to be broken down. It covers the algebraic inputs of the linear independence of the
distribution characters of irreducible admissible representations, stated on the page on
[smooth and admissible representations of p-adic groups](smooth-representations-of-p-adic-groups.md).
Let $G$ be an $\ell$-group with a Haar measure, $K$ a compact open subgroup, and
$\mathcal{H}(G, K) = e_K * C_c^\infty(G) * e_K$ the algebra of $K$-bi-invariant locally constant
compactly supported functions under convolution, with identity the normalized idempotent $e_K$ of $K$.

- **Corners.** For a smooth representation $(\pi, V)$, $\pi(e_K)$ is the projection of $V$ onto $V^K$, and
  $V^K$ is an $\mathcal{H}(G, K)$-module.
- **Simplicity.** If $V$ is irreducible and $V^K \ne 0$, then $V^K$ is a simple $\mathcal{H}(G, K)$-module.
- **Inequivalence survives.** If $V_1$ and $V_2$ are irreducible with $V_1^K \ne 0 \ne V_2^K$ and
  $V_1^K \cong V_2^K$ as $\mathcal{H}(G, K)$-modules, then $V_1 \cong V_2$.
- **Independence of characters.** Let $A$ be an algebra over $\mathbb{C}$ and $M_1, \dots, M_r$ pairwise
  non-isomorphic simple $A$-modules of finite dimension. Then $A$ maps onto
  $\prod_i \mathrm{End}_{\mathbb{C}}(M_i)$: each image is the full matrix algebra by Burnside's theorem, the
  kernels are pairwise distinct maximal two-sided ideals (a full matrix algebra has only one simple module
  up to isomorphism), and pairwise distinct maximal two-sided ideals are comaximal, so the Chinese remainder
  theorem for two-sided ideals applies. Hence the traces $a \mapsto \operatorname{trace}(a \mid M_i)$ are
  linearly independent.

Applied to finitely many pairwise inequivalent irreducible admissible representations and a compact open
$K$ small enough that every $V_i^K$ is nonzero (intersect finitely many stabilizers), these give the linear
independence of the distribution characters.

## Expansion

A good expansion has pages for the corner module $V^K$, for its simplicity, for the transfer of
inequivalence, and for the surjectivity onto the product of endomorphism algebras with the independence
of traces, each citing the sources below with locators.

It also writes out these steps of its own proof:

- the Chinese remainder theorem for pairwise comaximal two-sided ideals of a ring, for the surjectivity onto the product.
- the averaging projections $\pi(e_K)$ and the argument of Casselman's Proposition 2.2.2, for the corners, their simplicity and the transfer of inequivalence.

## Depends on

- [ℓ-spaces, distributions and smooth representations of ℓ-groups](l-spaces-distributions-and-smooth-representations-of-l-groups.md), for smooth representations of $\ell$-groups, the subspaces $V^K$ and admissibility
- [Haar measure](../../../MeasureTheory/haar-measure/is-haar-measure.md), for the Haar measure of the convolution product, under which $e_K$ is the indicator function of $K$ divided by its volume

## Proof depends on

- [Burnside's theorem on matrix algebras](../../../Algebra/associative-algebras/burnside-matrix.md), for the image of $A$ in each $\mathrm{End}_{\mathbb{C}}(M_i)$

## Sources

- W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, notes, draft of 1 May 1995, <https://personal.math.ubc.ca/~cass/research/pdf/p-adic-book.pdf>:
  §2.2, Proposition 2.2.2, Lemma 2.2.3 and Proposition 2.2.4 (the Hecke algebra $\mathcal{H}(G, K)$, the
  module $V^K$, its irreducibility, and the comparison of $G$-maps with $\mathcal{H}(G, K)$-maps), and
  §2.3, Proposition 2.3.1 (linear independence of distribution characters, "This is [23, Lemma 7.1]").
- H. Jacquet and R. P. Langlands, *Automorphic Forms on GL(2)*, Lecture Notes in Math. 114, Springer,
  1970, §7, Lemma 7.1, as cited by Casselman.
