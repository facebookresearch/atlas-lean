# Coefficient maps of square-integrable representations

This node is still to be broken down. It covers the Hilbert-space inputs of Godement's orthogonality
relations for square-integrable representations, which the page on
[discrete series representations and formal degrees](../reductive-groups-over-local-fields/representations-of-real-reductive-groups/discrete-series-and-formal-degrees.md)
states. Let $G$ be a locally compact unimodular group with Haar measure $dg$ and $(\pi, H)$ an
irreducible unitary representation of $G$, with inner products linear in the first variable.

- **Schur's lemma for unitary representations.** Every bounded operator on $H$ commuting with
  $\pi(G)$ is a scalar, and a bounded $G$-equivariant operator between two inequivalent irreducible
  unitary representations is zero.
- **Inversion.** $\int_G f(g^{-1}) \, dg = \int_G f(g) \, dg$ for every integrable $f$ on a unimodular
  $G$, so that $g \mapsto \langle \pi(g^{-1})\xi, \eta \rangle = \overline{\langle \pi(g)\eta, \xi \rangle}$
  and $g \mapsto \langle \pi(g)\eta, \xi \rangle$ have the same $L^2$-norm.
- **Coefficient maps.** If $g \mapsto \langle v, \pi(g)v \rangle$ is square-integrable for one
  $v \ne 0$, then every coefficient $g \mapsto \langle \pi(g)\xi, \eta \rangle$ is square-integrable,
  and for each $\eta$ the map $T_\eta \colon \xi \mapsto \langle \pi(\cdot)\xi, \eta \rangle$ is an
  everywhere defined closed, hence bounded, $G$-equivariant map from $H$ to $L^2(G)$ with the left
  regular representation; the passage from the initial coefficient to all vectors (through
  irreducibility, the closedness of the set of good vectors, or Carey's embedding of a cyclic
  representation into $L^2(G)$ by a positive-definite convolution square root) precedes the closed graph
  theorem, which applies only to an everywhere defined map.
- **Closed graph theorem.** A linear map between Banach spaces with closed graph is bounded.

A good expansion has pages for Schur's lemma for unitary representations (through the spectral
theorem), for the invariance of Haar measure under inversion on unimodular groups (beyond the
second-countable case already in the vault), for the closed graph theorem, and for the square
integrability of all coefficients and the boundedness of the coefficient maps, following Carey's proof
or Godement's, each citing the sources below with locators.

## Depends on

- Not yet a page: unitary representations of locally compact groups, the space $L^2(G)$ and the left regular representation, for all the items

## Proof depends on

- [Spectral theorem for bounded self-adjoint operators, multiplication form](../../Analysis/operator-theory/spectral-theory/spectral-theorem-for-bounded-self-adjoint-operat/bounded-self-adjoint-spectral-multiplica.md), for Schur's lemma: a self-adjoint operator commuting with $\pi(G)$ commutes with its spectral projections, which are then $0$ or $1$ by irreducibility; a commuting operator is a combination of two commuting self-adjoint ones, and for an intertwiner $T$ between inequivalent representations, $T^*T$ and $TT^*$ are such scalars
- [Right-invariant Haar measures are inversion-invariant](../../MeasureTheory/haar-measure/unimodular-groups/is-inv-invariant-of-is-mul-right-invaria.md), for the inversion, in the second-countable case, which covers Lie groups
- Not yet a page: the invariance of Haar measure under inversion on an arbitrary unimodular locally compact group, from the uniqueness of Haar measure up to a scalar, for Godement's general setting
- Not yet a page: the closed graph theorem for Banach spaces, for the boundedness of the coefficient maps

## Sources

- A. L. Carey, "Square-integrable representations of non-unimodular groups", Bull. Austral. Math.
  Soc. 15 (1976), 1–12, <https://doi.org/10.1017/S0004972700036728>: §1 (Godement's and Dixmier's
  orthogonality relations in the unimodular case) and §2 (square-integrable representations as the
  irreducible subrepresentations of the left regular representation, the embedding of a cyclic
  representation with a square-integrable diagonal coefficient, and the criterion through one such
  coefficient).
- A. I. Shtern, "Integrable representation", *Encyclopedia of Mathematics*,
  <http://encyclopediaofmath.org/index.php?title=Integrable_representation&oldid=51797>: the
  orthogonality relations for square-integrable representations of locally compact unimodular groups,
  citing G. Warner, *Harmonic analysis on semi-simple Lie groups* I, Springer, 1972, §4.5.9, and
  S. A. Gaal, *Linear analysis and representation theory*, Springer, 1973, Chapter VII.
- R. Godement, C. R. Acad. Sci. Paris 225 (1947), 521–523 and 657–659, the original proof, as cited
  by Carey.
