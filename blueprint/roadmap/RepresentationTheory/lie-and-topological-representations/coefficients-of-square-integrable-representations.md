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
- **Coefficient maps.** For $\eta \in H$ let $D_\eta$ be the space of $\xi$ such that
  $T_\eta \xi = \langle \pi(\cdot)\xi, \eta \rangle$ is square-integrable. Then
  $T_\eta(\pi(h)\xi)(g) = (T_\eta \xi)(gh)$: $T_\eta$ intertwines $\pi$ with the right regular representation
  $(R(h)f)(g) = f(gh)$, not with the left one (composing with $f \mapsto f(\cdot^{-1})$ gives the left one). The
  space $D_\eta$ is $\pi(G)$-invariant, and $T_\eta$ is closed on it: if $\xi_n \to \xi$ and $T_\eta \xi_n \to F$ in
  $L^2(G)$, then $T_\eta \xi_n \to T_\eta \xi$ pointwise and a subsequence converges to $F$ almost everywhere. If
  $D_\eta \ne 0$, it is dense by irreducibility, $\lvert T_\eta \rvert = (T_\eta^* T_\eta)^{1/2}$ is a positive self-adjoint
  operator commuting with $\pi(G)$, hence a scalar by its spectral projections, so $D_\eta = H$ and $T_\eta$ is
  bounded. Consequently, if $g \mapsto \langle \pi(g)v, v \rangle$ is square-integrable for one $v \ne 0$, then
  $D_v = H$; by inversion $v \in D_\xi$ for every $\xi$, so $D_\xi = H$ too: every coefficient
  $g \mapsto \langle \pi(g)\xi, \eta \rangle$ is square-integrable and every $T_\eta$ is a bounded $G$-equivariant map
  from $H$ to $L^2(G)$ with the right regular representation. Carey reaches the embedding into the regular
  representation through a positive-definite convolution square root; the passage from one coefficient
  to all of them uses the unimodularity of $G$, as here.
- **Closed operators.** A closed densely defined operator $T$ between Hilbert spaces has a
  [polar decomposition](../../Analysis/operator-theory/spectral-theory/unbounded-self-adjoint-and-trace-class-operators.md) $T = U \lvert T \rvert$, with $\lvert T \rvert$ positive
  self-adjoint and of the same domain as $T$.

## Expansion

A good expansion has pages for Schur's lemma for unitary representations (through the spectral
theorem), for the invariance of Haar measure under inversion on unimodular groups (beyond the
second-countable case), and for
the square integrability of all coefficients and the boundedness of the coefficient maps, each citing the sources below with locators.

It also writes out these steps of its own proof:

- the invariance of Haar measure under inversion on an arbitrary unimodular locally compact group: the image of a Haar measure under inversion is a right, hence left, Haar measure, a multiple $c$ of the original with $c^2 = 1$, for Godement's general setting.

## Depends on

- [Unitary representations of locally compact groups and representations of compact groups](unitary-representations-and-representations-of-compact-groups.md), for unitary representations of locally compact groups, the space $L^2(G)$ and its left and right regular representations, for all the items
- [Spectral theorem for unbounded self-adjoint operators, and trace-class operators](../../Analysis/operator-theory/spectral-theory/unbounded-self-adjoint-and-trace-class-operators.md), for the polar decomposition of closed densely defined operators

## Proof depends on

- [Spectral theorem for bounded self-adjoint operators, multiplication form](../../Analysis/operator-theory/spectral-theory/spectral-theorem-for-bounded-self-adjoint-operat/bounded-self-adjoint-spectral-multiplica.md), for Schur's lemma: a bounded operator $T$ commuting with $\pi(G)$ has self-adjoint parts $(T + T^*)/2$ and $(T - T^*)/2i$, each commuting with $\pi(G)$ as $\pi$ is unitary (they need not commute with each other); a self-adjoint operator commuting with $\pi(G)$ commutes with its spectral projections, which are then $0$ or $1$ by irreducibility; for an intertwiner $T$ between inequivalent representations, $T^*T$ and $TT^*$ are scalars, and a nonzero $T$ would be a multiple of a unitary equivalence
- [Right-invariant Haar measures are inversion-invariant](../../MeasureTheory/haar-measure/unimodular-groups/is-inv-invariant-of-is-mul-right-invaria.md), for the inversion, in the second-countable case, which covers Lie groups
- [Uniqueness of regular left-invariant measures up to a scalar](../../MeasureTheory/haar-measure/existence-and-uniqueness-of-haar-measure/is-mul-left-invariant-eq-smul-of-regular.md), for the uniqueness of Haar measure up to a scalar, behind the invariance under inversion
- [Spectral theorem for unbounded self-adjoint operators, and trace-class operators](../../Analysis/operator-theory/spectral-theory/unbounded-self-adjoint-and-trace-class-operators.md), for the polar decomposition of a closed densely defined operator $T$ between Hilbert spaces, with $\lvert T \rvert = (T^*T)^{1/2}$ of the same domain as $T$, and for the spectral projections of $\lvert T \rvert$ on an arbitrary, possibly nonseparable, Hilbert space, for the polar decomposition of the coefficient maps and their boundedness

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
