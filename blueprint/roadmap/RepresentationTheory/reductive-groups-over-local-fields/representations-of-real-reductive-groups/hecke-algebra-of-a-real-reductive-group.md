# The Hecke algebra of a real reductive group

This node is still to be broken down. It covers the archimedean local Hecke algebra in the definition of
automorphic representations. Let $G$ be the group of real points of a connected reductive group over
$\mathbb{R}$ (or over $\mathbb{C}$, viewed over $\mathbb{R}$), $K$ a maximal compact subgroup with
normalized Haar measure $dk$, $\mathfrak{g}$ and $\mathfrak{k}$ the complexified Lie algebras of $G$ and $K$,
and $\mathcal{U}(\mathfrak{g})$ the enveloping algebra.

- **The algebra.** The distributions on $G$ with support in $K$ that are $K$-finite under left and right
  translation form an algebra $\mathcal{H}(G, K)$ under convolution, which contains the algebra $\mathcal{A}(K)$
  of measures $f(k)\,dk$ with $f$ a $K$-finite function on $K$. When $K$ is infinite it does not contain
  $\mathcal{U}(\mathfrak{g})$: the distributions supported at the identity are not bi-$K$-finite, the translates of
  the Dirac distribution $\delta_e$ being the linearly independent point masses $\delta_k$. Instead
  $\mathcal{U}(\mathfrak{g})$, as distributions supported at the identity, acts on $\mathcal{H}(G, K)$ by left and right
  convolution, as multipliers; the convolutions $D * \xi$ with $D \in \mathcal{U}(\mathfrak{g})$ and
  $\xi \in \mathcal{A}(K)$ lie in $\mathcal{H}(G, K)$ and span it, and $D \otimes \xi \mapsto D * \xi$ induces a linear
  isomorphism $\mathcal{U}(\mathfrak{g}) \otimes_{\mathcal{U}(\mathfrak{k})} \mathcal{A}(K) \cong \mathcal{H}(G, K)$, the product
  being convolution of distributions.
- **Idempotents.** For an irreducible representation $\tau$ of $K$ with character $\chi_\tau$,
  $\xi_\tau = \dim(\tau)\, \overline{\chi_\tau(k)} \, dk$ is an idempotent, acting in the integrated action
  $\pi(\mu) = \int_K \pi(k) \, d\mu(k)$ as the projection onto the $\tau$-isotypic component (without the
  conjugate, for $K = \mathrm{U}(1)$ and $\tau(k) = k$, the measure $k \, dk$ projects onto the dual type). For a
  finite set $S$ of distinct irreducible $K$-types, $\xi_S = \sum_{\tau \in S} \xi_\tau$ is an idempotent; these
  form a directed family with $\mathcal{H}(G, K) = \bigcup_S \xi_S * \mathcal{H}(G, K) * \xi_S$, each corner having
  $\xi_S$ as identity. The same formula for a reducible $\delta$ is not an idempotent in general: for the sum of
  two trivial representations it gives $4 \, dk$, whose square is $16 \, dk$. The algebra has no identity when $K$
  is infinite; when $K$ is finite the Dirac measure at $1$ is one.
- **Modules.** $(\mathfrak{g}, K)$-modules are the same as nondegenerate $\mathcal{H}(G, K)$-modules, those $M$
  with $M = \bigcup_S \xi_S M$, the idempotent $\xi_\tau$ acting as the projection onto the
  $\tau$-isotypic component.

## Expansion

A good expansion has pages for the algebra of bi-$K$-finite distributions supported in $K$ with the
multiplier action of $\mathcal{U}(\mathfrak{g})$, for its description through
$\mathcal{U}(\mathfrak{g}) \otimes_{\mathcal{U}(\mathfrak{k})} \mathcal{A}(K)$, for the idempotents of irreducible
$K$-types, and for the equivalence of module categories, each citing a pinned source with locators
besides the one below.

## Depends on

- [Linear algebraic groups over local fields and their groups of rational points](../linear-algebraic-groups-over-local-fields.md), for the real points of a connected reductive group and their maximal compact subgroups
- [Harish-Chandra modules](harish-chandra-modules.md), for the definition of $(\mathfrak{g}, K)$-modules in the module item
- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for $K$-finite functions, isotypic components and the projections $\dim(\tau) \int_K \overline{\chi_\tau(k)}\, \pi(k) \, dk$
- [Vector-valued integrals and distributions on Lie groups](../../lie-and-topological-representations/vector-valued-integrals-and-distributions-on-lie-groups.md), for distributions on a Lie group, their convolution, and the enveloping algebra as the distributions supported at the identity, acting by convolution, for the algebra

## Proof depends on

- [Vector-valued integrals and distributions on Lie groups](../../lie-and-topological-representations/vector-valued-integrals-and-distributions-on-lie-groups.md), for the structure of distributions supported in $K$, through normal derivatives transverse to $K$, for the description of $\mathcal{H}(G, K)$ through $\mathcal{U}(\mathfrak{g}) \otimes_{\mathcal{U}(\mathfrak{k})} \mathcal{A}(K)$, with the product computed among distributions
- [Poincaré–Birkhoff–Witt theorem](../../../Algebra/nonassociative-algebras/poincare-birkhoff-witt-theorem.md), for the freeness of $U(\mathfrak{g})$ over $U(\mathfrak{k})$, through the ordered monomials in a basis of $\mathfrak{g}$ extending one of $\mathfrak{k}$, in that description
- [Unitary representations of locally compact groups and representations of compact groups](../../lie-and-topological-representations/unitary-representations-and-representations-of-compact-groups.md), for the Schur orthogonality relations for the characters of irreducible representations of a compact group, for the idempotents $\xi_\tau$

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 3, §1.0.1,
  pp. 21–22 (the local Hecke algebras as idempotented algebras without identity; at an archimedean place
  "the convolution algebra of bi-$K_v$-finite distributions on $G_v$ with support in $K_v$", with the
  shorthand $\mathcal{H}_v = \mathcal{U}(\mathfrak{g}_v) \otimes_{\mathcal{U}(\mathfrak{k}_v)} \mathcal{A}(K_v)$ and fundamental
  idempotents $\xi_{\delta_v}$ written with the degree and the character of $\delta_v$; the multiplier description
  and the normalization for irreducible types above make this shorthand precise).
