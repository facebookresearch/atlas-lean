# The Hecke algebra of a real reductive group

This node is still to be broken down. It covers the archimedean local Hecke algebra in the definition of
automorphic representations. Let $G$ be the group of real points of a connected reductive group over
$\mathbb{R}$ (or over $\mathbb{C}$, viewed over $\mathbb{R}$), $K$ a maximal compact subgroup with
normalized Haar measure $dk$, $\mathfrak{g}$ and $\mathfrak{k}$ the complexified Lie algebras of $G$ and $K$,
and $\mathcal{U}(\mathfrak{g})$ the enveloping algebra.

- **The algebra.** The distributions on $G$ with support in $K$ that are $K$-finite under left and right
  translation form an algebra $\mathcal{H}(G, K)$ under convolution. It contains $\mathcal{U}(\mathfrak{g})$, as
  the distributions supported at the identity, and the algebra $\mathcal{A}(K)$ of measures $f(k)\,dk$
  with $f$ a $K$-finite function on $K$, and multiplication induces an isomorphism
  $\mathcal{U}(\mathfrak{g}) \otimes_{\mathcal{U}(\mathfrak{k})} \mathcal{A}(K) \cong \mathcal{H}(G, K)$.
- **Idempotents.** For a finite-dimensional representation $\delta$ of $K$ with character $\Theta_\delta$,
  $\xi_\delta = \deg(\delta)\, \Theta_\delta \, dk$ is an idempotent; for finite sets of $K$-types these
  idempotents form a directed family with $\mathcal{H}(G, K) = \bigcup \xi * \mathcal{H}(G, K) * \xi$, each
  $\xi * \mathcal{H}(G, K) * \xi$ having $\xi$ as identity. The algebra has no identity when $K$ is
  infinite; when $K$ is finite the Dirac measure at $1$ is one.
- **Modules.** $(\mathfrak{g}, K)$-modules are the same as nondegenerate $\mathcal{H}(G, K)$-modules, those $M$
  with $M = \bigcup_\xi \xi M$, the idempotent $\xi_\delta$ acting as the projection onto the
  $\delta$-isotypic component.

A good expansion has pages for the algebra of bi-$K$-finite distributions supported in $K$, for the
isomorphism with $\mathcal{U}(\mathfrak{g}) \otimes_{\mathcal{U}(\mathfrak{k})} \mathcal{A}(K)$, for the
idempotents, and for the equivalence of module categories, each citing a pinned source with locators
besides the one below.

## Depends on

- Not yet a page: distributions on a Lie group, their convolution, and the enveloping algebra as the distributions supported at the identity, for the algebra
- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for $K$-finite functions and isotypic components

## Proof depends on

- Not yet a page: the structure theory of distributions with compact support on a Lie group near a compact subgroup, for the isomorphism with $\mathcal{U}(\mathfrak{g}) \otimes_{\mathcal{U}(\mathfrak{k})} \mathcal{A}(K)$
- Not yet a page: the Schur orthogonality relations for the characters of $K$, for the idempotents

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 3, §1.0.1,
  pp. 21–22 (the local Hecke algebras as idempotented algebras without identity; at an archimedean place
  "the convolution algebra of bi-$K_v$-finite distributions on $G_v$ with support in $K_v$", containing
  $\mathcal{U}(\mathfrak{g})$ and $\mathcal{A}(K_v)$, with
  $\mathcal{H}_v = \mathcal{U}(\mathfrak{g}_v) \otimes_{\mathcal{U}(\mathfrak{k}_v)} \mathcal{A}(K_v)$, and the
  idempotents $\xi_{\delta_v}$).
