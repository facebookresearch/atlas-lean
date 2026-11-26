# Smooth vectors and K-finite vectors of continuous representations

This node is still to be broken down. It covers the basic facts on continuous representations of Lie
groups and of their compact subgroups that the pages on real reductive groups use. Let $G$ be a Lie
group with a left Haar measure $dg$, $(\pi, V)$ a continuous representation of $G$ on a complete
locally convex Hausdorff complex vector space $V$ (a Fréchet space where stated) and $K$ a compact subgroup of $G$
with Haar measure of total mass $1$.

- **Integrated action and smoothing.** For $f \in C_c(G)$ and $v \in V$ the integral
  $\pi(f)v = \int_G f(g)\pi(g)v \, dg$ converges in $V$, and $\pi(f_1 * f_2) = \pi(f_1)\pi(f_2)$. A vector
  $v$ is smooth if $g \mapsto \pi(g)v$ is a smooth map $G \to V$; for $f \in C_c^\infty(G)$ the vector
  $\pi(f)v$ is smooth. The smooth vectors $V^\infty$ form a $G$-stable subspace on which the Lie
  algebra of $G$ acts by derivatives.
- **Dirac sequences and density** (Gårding). There are nonnegative $f_n \in C_c^\infty(G)$ with
  $\int_G f_n = 1$ whose supports shrink to $\{1\}$; for such a sequence $\pi(f_n)v \to v$ for every
  $v \in V$. Hence $V^\infty$, and the Gårding subspace spanned by the vectors $\pi(f)v$ with
  $f \in C_c^\infty(G)$, are dense in $V$.
- **$K$-types.** For an irreducible representation $\tau$ of $K$ with character $\chi_\tau$, the
  operator $E_\tau = \dim(\tau) \int_K \overline{\chi_\tau(k)}\, \pi(k) \, dk$ is a continuous
  projection of $V$ onto its $\tau$-isotypic subspace $V(\tau)$, commuting with $\pi(K)$, and
  $E_\tau E_{\tau'} = 0$ for $\tau \not\cong \tau'$. The space $V_K$ of $K$-finite vectors, the
  algebraic direct sum of the $V(\tau)$, is dense in $V$; so is $V^\infty \cap V_K$ when $K$ is a
  compact subgroup of the Lie group $G$.
- **Unitary case.** For a unitary representation of $K$ on a Hilbert space, $V$ is the Hilbert
  direct sum of the mutually orthogonal subspaces $V(\tau)$; for the regular representation on
  $L^2(K)$ this is the Peter–Weyl theorem, and the matrix coefficients of the finite-dimensional
  representations of $K$ are dense in $C(K)$ for the uniform norm.

## Expansion

A good expansion has pages for the integrated action and the smoothness of $\pi(f)v$, for Dirac
sequences on Lie groups, for the density of smooth vectors, for the isotypic projections and the
density of $K$-finite vectors (from the density of matrix coefficients in $C(K)$, which follows from
[point separation](representations-of-compact-groups/peter-weyl-point-separation.md) by the complex
Stone–Weierstrass theorem, the coefficients forming a unital algebra closed under conjugation), and
for the Hilbert direct sum in the unitary case, each citing the sources below with locators.

## Depends on

- [Lie group](../../Geometry/differential-topology/lie-group.md), for Lie groups, for all the items
- [Haar measure](../../MeasureTheory/haar-measure/is-haar-measure.md), for their Haar measures
- [Lie groups: the exponential map, closed subgroups and maximal compact subgroups](lie-groups-exponential-map-and-maximal-compact-subgroups.md), for their Lie algebras and the exponential map
- [Vector-valued integrals and distributions on Lie groups](vector-valued-integrals-and-distributions-on-lie-groups.md), for integrals of continuous compactly supported functions with values in a complete locally convex space
- [Unitary representations of locally compact groups and representations of compact groups](unitary-representations-and-representations-of-compact-groups.md), for irreducible representations of compact groups and their characters, for the isotypic subspaces and projections

## Proof depends on

- [Peter–Weyl theorem: unitary representations separate points](representations-of-compact-groups/peter-weyl-point-separation.md), for the density of the matrix coefficients in $C(K)$, through the Stone–Weierstrass theorem
- [Representations of compact groups are semisimple](representations-of-compact-groups/compact-group-semisimple.md), for the complete reducibility of the finite-dimensional $K$-stable subspaces spanned by $K$-finite vectors (its real form; the complex case is the same argument with an invariant Hermitian form)
- [Stone–Weierstrass theorem for star subalgebras](../../Topology/function-spaces/stone-weierstrass-star-subalgebra.md), for the density of the matrix coefficients
- [Vector-valued integrals and distributions on Lie groups](vector-valued-integrals-and-distributions-on-lie-groups.md), for differentiation under the integral sign for vector-valued integrals, applied to $g \mapsto \pi(g)\pi(f)v = \int_G f(g^{-1}x)\pi(x)v \, dx$, the translated smoothing kernel, not to $g \mapsto \pi(g)v$ itself, for the smoothness of $\pi(f)v$
- [Unitary representations of locally compact groups and representations of compact groups](unitary-representations-and-representations-of-compact-groups.md), for the Schur orthogonality relations for the characters of a compact group, for $E_\tau^2 = E_\tau$ and $E_\tau E_{\tau'} = 0$

## Sources

- P. Etingof, "Representations of Lie groups", lecture notes, arXiv:2401.01446 (version 3): §4.2,
  Lemma 4.5 (Dirac sequences, smooth ones on Lie groups) and Corollary 4.6; §4.3, Corollary 4.7
  (density of the $K$-finite vectors in a continuous representation of a compact group, through Dirac
  sequences and the Peter–Weyl theorem) and Corollary 4.8; Definition 4.11 and Proposition 4.15 (smooth
  vectors and their density).
- W. Casselman, "Canonical extensions of Harish-Chandra modules to representations of G", Canad. J.
  Math. 41 (1989), 385–438, <https://doi.org/10.4153/CJM-1989-019-5>: §1, p. 391 (smooth vectors, the
  operators $\pi(f)$, the Gårding subspace, and "The intersection $V^{\mathrm{sm}} \cap V_K$ is dense in V
  and stable under both g and K"), and the proof of Proposition 2.2, p. 394 (the continuous projections
  onto $K$-isotypic components).
