# Vector-valued integrals and distributions on Lie groups

This node is still to be broken down. It covers the analysis on Lie groups that the pages on smooth and
$K$-finite vectors, on the Dixmier–Malliavin lemma and on the Hecke algebra of a real reductive group use.
Let $G$ be a real [Lie group](../../Geometry/differential-topology/lie-group.md) with a left [Haar measure](../../MeasureTheory/haar-measure/is-haar-measure.md) $dg$ and Lie algebra
$\mathfrak{g}$.

- **Vector-valued integrals.** For a quasi-complete locally convex space $V$ (for instance a Fréchet or Hilbert
  space) and a continuous compactly supported $f \colon G \to V$, there is a unique $\int_G f \, dg \in V$ with
  $\lambda(\int_G f \, dg) = \int_G \lambda \circ f \, dg$ for every continuous linear form $\lambda$; it lies in the
  closed convex hull of the image of $f$ scaled by the measure of the support, and continuous linear maps
  commute with it.
- **Differentiation under the integral sign.** If $F \colon G \times G \to V$ is continuous, smooth in its first
  variable with all derivatives continuous on $G \times G$, and supported in $G \times C$ for a compact $C$, then
  $g \mapsto \int_G F(g, x) \, dx$ is smooth and its derivatives are the integrals of the derivatives of $F$.
- **Distributions.** A distribution on $G$ is a continuous linear form on $C_c^\infty(G)$; the compactly supported
  ones convolve, by $(S * T)(\varphi) = S_x T_y \varphi(xy)$, into an associative algebra. A sequence of
  distributions supported in a fixed compact set converges weakly if it converges on every test function.
- **The enveloping algebra at the identity.** The distributions supported at $1$ form a subalgebra isomorphic to
  the [universal enveloping algebra](../../Algebra/nonassociative-algebras/universal-enveloping-algebra.md) $U(\mathfrak{g}_{\mathbb{C}})$: the element
  $X_1 \cdots X_n$ corresponds to $\varphi \mapsto \partial_{t_1} \cdots \partial_{t_n}
  \varphi(\exp(t_1X_1) \cdots \exp(t_nX_n))|_{t = 0}$.
- **Distributions supported on a compact subgroup.** For a compact subgroup $K$ with Lie algebra $\mathfrak{k}$, every
  distribution supported in $K$ is a finite sum of derivatives transverse to $K$ of distributions on $K$, and the
  distributions supported in $K$ that are finite under left and right translation by $K$ form the algebra
  $U(\mathfrak{g}_{\mathbb{C}}) \otimes_{U(\mathfrak{k}_{\mathbb{C}})} \mathcal{A}(K)$, with $\mathcal{A}(K)$ the $K$-finite
  distributions on $K$.

## Expansion

A good expansion has statement pages for the Gelfand–Pettis integral and its properties, for
differentiation under the integral sign for vector-valued integrals, for distributions on a Lie group and
their convolution, for the identification of $U(\mathfrak{g}_{\mathbb{C}})$ with the distributions supported at
the identity, and for the structure of the distributions supported in a compact subgroup, each citing the
sources below with locators. The last rests on L. Schwartz's local structure theorem for distributions
supported in a submanifold, which such a page cites with its locator, and on the Poincaré–Birkhoff–Witt
theorem, which turns the normal derivatives into $U(\mathfrak{g}_{\mathbb{C}}) \otimes_{U(\mathfrak{k}_{\mathbb{C}})} \mathcal{A}(K)$.

## Depends on

- [Lie group](../../Geometry/differential-topology/lie-group.md), for the setting
- [Haar measure](../../MeasureTheory/haar-measure/is-haar-measure.md), for the integrals
- [Universal enveloping algebra of a Lie algebra](../../Algebra/nonassociative-algebras/universal-enveloping-algebra.md), for the distributions at the identity
- [Lie groups: the exponential map, closed subgroups and maximal compact subgroups](lie-groups-exponential-map-and-maximal-compact-subgroups.md), for the
  exponential map and closed subgroups

## Proof depends on

- [Smoothness of compactly supported parameter integrals](../../MeasureTheory/integration/differentiation-under-the-integral-sign/smoothness-of-parameter-integrals/cont-diff-integral-smul-comp-of-cont-dif.md), for differentiation under the
  integral sign in the Banach-valued case

## Sources

- P. Garrett, "Unitary representations of topological groups", notes, 3 August 2014,
  <https://www-users.cse.umn.edu/~garrett/m/repns/notes_2014-15/06a_unitary_of_top.pdf>: §6, Theorem [6.0.1], Corollary [6.0.3] and Remark [6.0.4] (Gelfand–Pettis integrals of compactly
  supported continuous functions with values in a Hilbert space, the compatibility with continuous linear maps,
  and their validity for quasi-complete locally convex spaces).
- P. Etingof, "Representations of Lie groups", lecture notes, arXiv:2401.01446 (version 3), <https://arxiv.org/abs/2401.01446>: §3 (algebras of measures on locally compact groups, their support and convolution) and §4.4
  (smooth vectors).
- P. Etingof, "Lie groups and Lie algebras", lecture notes, arXiv:2201.09397 (version 5), <https://arxiv.org/abs/2201.09397>: §12.4 (differential operators on manifolds and Lie groups; $U(\mathfrak{g})$ as the left-invariant
  differential operators) and §13.1, Theorem 13.1 (the Poincaré–Birkhoff–Witt theorem).
- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in *Lectures on
  Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society, 2004; author's version
  <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 3, §1.0.1, pp. 21–22 (the archimedean Hecke
  algebra as the bi-$K$-finite distributions supported in $K$, written
  $\mathcal{U}(\mathfrak{g}) \otimes_{\mathcal{U}(\mathfrak{k})} \mathcal{A}(K)$).
