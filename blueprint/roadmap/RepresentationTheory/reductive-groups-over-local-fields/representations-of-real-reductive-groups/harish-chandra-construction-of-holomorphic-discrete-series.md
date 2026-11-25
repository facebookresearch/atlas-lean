# Harish-Chandra's construction of the holomorphic discrete series

This node is still to be broken down. It covers the analytic inputs of the theorem on the
[holomorphic discrete series](holomorphic-discrete-series.md), in the setting and notation of that page:
$G$ with compact centre, $K$, the compact Cartan subgroup $H$, the positive system $\Psi$, the
splitting $\mathfrak{p} = \mathfrak{p}_+ \oplus \mathfrak{p}_-$, the subgroups $P_\pm$ of $G^{\mathbb{C}}$,
the parabolic subgroup $K^{\mathbb{C}} P_+$, the $K$-module $V_\mu$ and the $G$-module $\mathbf{F}_\lambda$
of holomorphic sections over $G/K \subseteq G^{\mathbb{C}}/K^{\mathbb{C}} P_+$.

- **The Harish-Chandra embedding.** $G$ lies in the open subset $P_- K^{\mathbb{C}} P_+$ of
  $G^{\mathbb{C}}$, on which the product map $P_- \times K^{\mathbb{C}} \times P_+ \to G^{\mathbb{C}}$ is
  injective, and $g \mapsto \log$ of the $P_-$-component of $g$ identifies $G/K$ with a bounded domain
  $\mathcal{D}$ in $\mathfrak{p}_-$.
- **Polynomial model.** Through this trivialization, holomorphic sections of the bundle defined by
  $V_\mu$ become holomorphic $V_\mu$-valued functions on $\mathcal{D}$, and the $K$-finite ones are the
  polynomial functions. As $\mathfrak{p}_+$ and $\mathfrak{p}_-$ are mutually dual, the polynomial
  functions on $\mathfrak{p}_-$ form a $K$-module isomorphic to the symmetric algebra $S(\mathfrak{p}_+)$,
  so the $K$-finite vectors of $\mathbf{F}_\lambda$ form $V_\mu \otimes S(\mathfrak{p}_+)$; Schmid also
  describes $\mathbf{F}_\lambda$, up to infinitesimal equivalence, on $V_\mu \otimes H^2(S)$, $S$ the
  Shilov boundary, in which the polynomial functions are dense.
- **Fréchet topology.** With the topology of uniform convergence on compact subsets, the space of
  holomorphic sections is a Fréchet space: $G/K$ has a countable exhaustion by compact sets, and
  locally uniform limits of holomorphic functions are holomorphic. $G$ acts continuously by translation.
- **The lowest $K$-type.** Every nonzero closed $G$-invariant subspace $W$ of $\mathbf{F}_\lambda$ contains
  $V_\mu$: after a translation some section in $W$ is nonzero at the base point; evaluation at the base
  point is a $K$-equivariant map onto the irreducible fibre $V_\mu$, nonzero on the $V_\mu$-isotypic
  part of $W$ (obtained by the continuous isotypic projection), which is contained in the unique copy
  of $V_\mu$ in $\mathbf{F}_\lambda$.
- **Square-integrability** (Harish-Chandra). Fix a $G$-invariant measure on $G/K$ and a $K$-invariant
  Hermitian inner product on $V_\mu$, which give the Hilbert space of square-integrable sections of the
  bundle. If $(\lambda, \alpha) > 0$ for every $\alpha \in \Psi$, the square-integrable holomorphic sections form a
  nonzero $G$-invariant subspace of this Hilbert space, closed in it (on each compact set holomorphic sections
  are bounded uniformly by a multiple of their $L^2$ norm, by the mean value property, so $L^2$ limits of
  holomorphic sections are holomorphic), on which $G$ acts by a discrete series representation
  infinitesimally equivalent to $\mathbf{F}_\lambda$ (Schmid, (3.12)). This subspace need not be closed in
  $\mathbf{F}_\lambda$ for the topology of uniform convergence on compact sets: for $\mathrm{SU}(1, 1)$ in the scalar
  case of weight $2$ it is the Bergman space of the disk, which contains the partial sums of
  $\sum_j z^j$, and these converge uniformly on compact sets to $1/(1 - z)$, which is not square-integrable; for a
  compact group $G = K$, such as $\mathrm{SU}(2)$, $G/K$ is a point and the finite-dimensional space of sections is closed
  in both topologies.

## Expansion

A good expansion has pages for the decomposition $P_- K^{\mathbb{C}} P_+$ and the bounded realization,
for the polynomial model with the duality of $\mathfrak{p}_\pm$, for the Fréchet topology of spaces of
holomorphic sections, for the lowest $K$-type argument, and for Harish-Chandra's square-integrability
criterion, each citing the sources below with locators.

It also writes out these steps of its own proof:

- the passage from one to several variables: a locally uniform limit of holomorphic functions on an open subset of $\mathbb{C}^n$ is continuous and, by the one-variable theorem on slices, holomorphic in each variable separately; Osgood's lemma in its local form, proved by the iterated one-variable Cauchy integral over the distinguished boundary of a closed polydisc inside the open set, makes it holomorphic, for the Fréchet topology.
- Harish-Chandra's construction of the square-integrable holomorphic sections (Harish-Chandra IV–VI), for the square-integrability: the nonvanishing of the Hilbert space under positivity and its infinitesimal equivalence with $\mathbf{F}_\lambda$ (Schmid, §3, (3.12), pp. 72–73).

## Depends on

- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for $K$-finite vectors and isotypic components
- [Hermitian symmetric spaces and their compact duals](hermitian-symmetric-spaces.md), for Hermitian symmetric spaces $G/K$, compact Cartan subgroups and compact and noncompact roots, the complexification $G^{\mathbb{C}}$ and its compact dual, and homogeneous holomorphic vector bundles, for all the items

## Proof depends on

- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for the continuous isotypic projections in the lowest $K$-type argument
- [Locally uniform limits of holomorphic functions are holomorphic](../../../Analysis/complex-analysis/cauchy-theory/locally-uniform-limit-of-holomorphic.md), for the Weierstrass theorem in one variable, for the Fréchet topology

## Sources

- W. Schmid, "On the characters of the discrete series. The Hermitian symmetric case", Invent. Math.
  30 (1975), 47–144, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0030>: §3, (3.1)–(3.9),
  pp. 70–71 (the splitting $\mathfrak{p}_\pm$, the embedding of $G/K$ in its compact dual, $V_\mu$ and the
  Fréchet $G$-modules $\mathbf{F}_\lambda$, the $K$-type $V_\mu$ in every closed $G$-invariant subspace),
  pp. 72–73, (3.12) (the discrete series under positivity, after Harish-Chandra), and §7, p. 125 ("Via
  the Harish-Chandra embedding, $G/K$ can be realized as a bounded domain in $\mathfrak{p}_-$"; the
  Shilov boundary and $H^2(S)$; "Since $\mathfrak{p}_+$ and $\mathfrak{p}_-$ are mutually dual, the
  polynomial algebra is $K$-isomorphic to the symmetric algebra of $\mathfrak{p}_+$"; the $K$-structure
  "proven in Harish-Chandra's original construction of the 'holomorphic discrete series'").
- Harish-Chandra, "Representations of semi-simple Lie groups" IV–VI, Amer. J. Math. 77 (1955) and 78
  (1956), the original construction, as cited by Schmid.
