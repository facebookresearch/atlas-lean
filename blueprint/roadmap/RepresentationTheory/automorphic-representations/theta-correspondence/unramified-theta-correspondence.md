# Unramified theta correspondence

This node is still to be broken down. It covers the local theta correspondence for unramified dual pairs
over a non-archimedean local field $F$ of characteristic $0$: the dual pair, the additive character $\psi$
(trivial on $\mathcal{O}_F$ and not on $\mathfrak{p}^{-1}$) and the splitting characters are unramified,
and the spaces contain self-dual lattices, so that both groups of the pair have hyperspecial maximal
compact subgroups $K$ and $K'$ fixing the vacuum vector $\varphi_0$ of the lattice model of the
[Weil representation](weil-representation-of-unitary-dual-pairs.md).

- **Spherical vectors** (Howe). The vectors of the Weil representation fixed by $K'$ are those generated
  from $\varphi_0$ by the action of the other group of the pair, and symmetrically; in the Schrödinger model
  of a unitary dual pair, a vector fixed by the integral points of one unitary group lies in the span of the
  translates of $\varphi_0$ by the other.
- **Unramified representations correspond** (Howe). In the theta correspondence of an unramified dual
  pair, a representation with a non-zero $K$-fixed vector corresponds to one with a non-zero $K'$-fixed
  vector.
- **Satake parameters** (Rallis). The matching of unramified representations is explicit in terms of
  Satake parameters, and is given by an $L$-homomorphism between the $L$-groups.

A good expansion has pages for the lattice model and the vacuum vector, for Howe's statements on spherical
vectors and on the correspondence of unramified representations, and for the explicit matching of Satake
parameters for unitary dual pairs, each with a precise statement and a source with locators. Kudla's
notes treat the symplectic–orthogonal case; the unitary case should be sourced from Mœglin, Vignéras and
Waldspurger's treatment of unramified dual pairs or from a published account of the unitary case, checked
against the statement used.

## Depends on

- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for the Weil representation of a unitary dual pair
- [Howe duality for unitary dual pairs over p-adic fields](howe-duality-over-p-adic-fields.md), for the local theta correspondence
- [Borel–Casselman theorem on Iwahori-fixed vectors](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/borel-casselman-theorem.md), for unramified representations as constituents of unramified principal series

## Sources

- S. S. Kudla, "Notes on the local theta correspondence", lecture notes, European School in Group
  Theory, 1996, <https://www.math.toronto.edu/~skudla/castle.pdf>: §VI.3 ("A basic result of Howe [24],
  [26], is that, in the theta correspondence for unramified dual pairs (G, H), [46], unramified
  representations are matched with unramified representations", and Proposition 3.2, Rallis's explicit
  matching for $(\mathrm{O}(V), \mathrm{Sp}(W))$), §VI.4 (the $L$-homomorphism and Rallis's theorem). The
  references are R. Howe, "θ-series and invariant theory", Proc. Sympos. Pure Math. 33, Part 1, 1979,
  275–285, and "Another look at the local theta correspondence for an unramified dual pair", Festschrift
  in honor of I. I. Piatetski-Shapiro, vol. 2, Israel Math. Conf. Proc., 1990, 93–124; C. Mœglin, M.-F. Vignéras and J.-L. Waldspurger, *Correspondances de Howe sur un
  corps p-adique*, Lecture Notes in Math. 1291, Springer, 1987; S. Rallis, "Langlands' functoriality and
  the Weil representation", Amer. J. Math. 104 (1982), 469–515.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the spherical-vector statement for unitary dual pairs as `GlobalTheory.Hk3.HoweUnram`, proved as
  `howeUnram_holds`.
