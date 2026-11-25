# Explicit formulas for the Weil representation

This node is still to be broken down. It covers the explicit structure of the local Weil representation
that the [metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md)
and the [Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md) use, over a
local field $F$ of characteristic different from $2$ and a symplectic space $W$ over $F$.

- **Cocycles.** The Leray invariant and the normalized cocycle of Rao on $\mathrm{Sp}(W)$, defined from a
  symplectic basis; the explicit operators $r(g)$ of the Schrödinger model for all block ranks of $g$, and
  the formula expressing the Weil representation as a genuine representation of the twofold cover in terms
  of this cocycle.
- **Twofold cover and non-splitting.** The reduction of the $\mathbb{C}^\times$-extension $\mathrm{Mp}(W)$ to a
  twofold cover, its independence of $\psi$ at a non-archimedean place, and its non-splitting when $\dim_F W \ge 2$ and
  $F$ is either non-archimedean or $\mathbb{R}$ (reduced to a symplectic plane); over $F = \mathbb{C}$ the
  cocycle is trivial and the extension splits (Rao, Proposition 5.8); the splitting of the
  $\mathbb{C}^\times$-extension over the stabilizer $P_Y$ of a maximal isotropic subspace.
- **Fock model.** At a real place, the Fock model of the oscillator representation, its
  $\tilde{\mathrm U}(n)$-finite vectors and the operators by which $\mathfrak{sp}_{\mathbb{C}}$ acts on them.
- **Splittings for unitary dual pairs.** For a quadratic extension $E/F$ (or $E = F \times F$), the splittings
  over $\mathrm{U}(V) \times \mathrm{U}(W)$ of the $\mathbb{C}^1$-extension $\mathrm{Mp}^{(2)}(W) \times_{\mu_2} \mathbb{C}^1$ (the pushout of the
  twofold cover along $\mu_2 \subset \mathbb{C}^1$, whose further pushout along $\mathbb{C}^1 \subset \mathbb{C}^\times$ is the
  $\mathbb{C}^\times$-extension) determined by splitting characters, their restriction to the Levi factors of the stabilizers of
  doubled diagonal subspaces (Kudla's theorem), Hilbert's theorem 90 for the character twists, the
  compatibility of local splittings almost everywhere and the product formula for the global splitting
  (for a split skew-Hermitian space, Kudla's Theorem 3.1; nonsplit spaces are handled through doubling),
  and the doubling intertwiner between the Schrödinger models of a polarization and of the doubled
  polarization, with evaluation at zero giving the inner product.

- **Product formula for Weil indices.** For a non-degenerate quadratic form $q$ over a number field $F$ and a
  single non-trivial character $\psi = \prod_v \psi_v$ of $\mathbb{A}_F/F$, the local Weil indices $\gamma_{\psi_v}(q_v)$ are almost all $1$ and
  their product is $1$ (Weil, §§29–30, Proposition 5). The local characters cannot be chosen independently: for
  $q = x^2$ over $\mathbb{Q}$, replacing only the real component of $\psi$ by its inverse changes the real index between
  $e^{\pi i/4}$ and $e^{-\pi i/4}$ (Weil, §26), which multiplies the product by $e^{\mp \pi i/2} \ne 1$ ($-i$ if the real component
  was $t \mapsto e^{2\pi i t}$, $+i$ if it was its inverse). From the product formula
  Hilbert reciprocity follows by taking the norm form of a quaternion algebra (Weil calls reciprocity formally
  weaker); through it the rational points of $\mathrm{Sp}(W)$ lift to the twofold cover of the adelic group (Weil, §45).

## Expansion

A good expansion has pages for Rao's cocycle and the explicit formulas, for the twofold cover and its
non-splitting, for the real Fock model, for Kudla's splittings of unitary dual pairs and their global
compatibility, for the doubling intertwiner, and for the product formula for Weil indices, each with a
precise statement and the sources below.

A good expansion also writes out these steps of its own proof:

- the specialization of Weil's theorems on characters of the second degree to $G = X_{\mathbb{A}}$, $\Gamma = X_F$ and $f = \psi \circ q$: Théorème 5 gives $\gamma(q) = 1$, and Corollaire 2 of Théorème 2, applied to a factorizable Schwartz–Bruhat function and to its local factors, almost all the characteristic functions of the unit lattices, gives $\gamma(q) = \prod_v \gamma_{\psi_v}(q_v)$ (§30, the proof of Proposition 5, p. 179), for the product formula for Weil indices.

## Depends on

- [Stone–von Neumann theorem for Heisenberg groups over local fields](stone-von-neumann-theorem.md), for the Heisenberg representation whose normalizer defines the Weil representation
- [Additive duality of adeles and the volume of A/K](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/additive-duality-of-adeles.md), for the global additive characters of $\mathbb{A}_F/F$ and their local components, used in the product formula for Weil indices

## Proof depends on

- [Hilbert's Theorem 90 for the multiplicative group](../../../FieldTheory/galois-theory/multiplicative-hilbert-s-theorem-90.md), for the character twists of the splittings when $E/F$ is a quadratic field extension, through the norm-one elements $x/\sigma(x)$ (Harris–Kudla–Sweet, (1.7)–(1.8)); for the split algebra $E = F \times F$ the analogous map is $(a, b) \mapsto (a/b, b/a)$, with no field extension
- [Additive duality of adeles and the volume of A/K](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/additive-duality-of-adeles.md), for the self-duality of $\mathbb{A}_F$ under which $F$ is its own annihilator, which Weil extends to $X_{\mathbb{A}}$ and $X_F$ coordinatewise (Weil, §29, p. 178)
- [Weil's theorems on characters of the second degree](../../../Analysis/harmonic-analysis/weil-characters-of-the-second-degree.md), for Weil's Théorème 5 (§20, p. 169), the triviality of the Weil index of a character of the second degree trivial on a closed subgroup that its symmetric morphism maps onto the orthogonal, and Corollaire 2 of his Théorème 2 (§14, p. 162), which the product formula for Weil indices specializes to the adelic quadratic space

## Sources

- R. Ranga Rao, "On some explicit formulas in the theory of Weil representation", Pacific J. Math. 157
  (1993), no. 2, <https://doi.org/10.2140/pjm.1993.157.335>: introduction (any self-dual locally compact
  field of characteristic different from $2$), Lemma 3.2, Theorem 3.5, Theorem 4.1, Theorem 5.3,
  Proposition 5.8 (the multiplier is trivial over $\mathbb{C}$) and the Appendix (the cocycle and the explicit formulas).
- A. Weil, "Sur certains groupes d'opérateurs unitaires", Acta Math. 111 (1964), 143–211,
  <https://doi.org/10.1007/BF02391012>: §30, Proposition 5 and the remarks after it (the product formula for
  Weil indices for one global character, Hilbert reciprocity as a formally weaker consequence), §26 (the real
  indices $e^{\pm \pi i/4}$), §29 (the global character and its local components; p. 178, the self-duality of the adeles in
  which the field is its own dual), §45 (the rational lift in the twofold cover); and, for the proof of Proposition 5 (p. 179),
  §14, Théorème 2 and its Corollaire 2 (pp. 161–162), and §20, Théorème 5 and its proof (p. 169), which goes
  back to the proof of Théorème 2 and uses that $r_\Gamma$ is a representation; §19, Théorème 4 (p. 168), and the remark before
  Théorème 5 that it contains Poisson's formula, are related.
- S. S. Kudla, "Notes on the local theta correspondence", lecture notes, European School in Group
  Theory, 1996, <https://www.math.toronto.edu/~skudla/castle.pdf>: §I.4, Theorem 4.5, Corollaries 4.8 and
  4.9 (the twofold cover via the Rao cocycle), §I.6, Lemma 6.1 (the $\mathbb{C}^\times$-extension splits over
  $P_Y$) and Proposition 6.6 (non-triviality, proved by restriction to a symplectic plane).
- S. S. Kudla, "Splitting metaplectic covers of dual reductive pairs", Israel J. Math. 87 (1994), 361–401,
  Theorem 3.1, as cited by Harris–Kudla–Sweet (§1) and by Gan–Qiu–Takeda (§2.8).
- R. Howe, "Transcending classical invariant theory", J. Amer. Math. Soc. 2 (1989), 535–552,
  <https://doi.org/10.1090/S0894-0347-1989-0985172-6>: §2, (2.1)–(2.3) (the Fock model).
- J.-S. Li, "Non-vanishing theorems for the cohomology of certain arithmetic quotients", J. Reine Angew.
  Math. 428 (1992), 177–217: §2, p. 181, (10), and p. 182, (12)–(13) (the doubling isometry and its value
  at zero), as cited by Gan–Qiu–Takeda (§11.3).
- C. Wu, "Irreducibility of theta lifting for unitary groups",
  arXiv:1409.0770 (preprint version): §2.1–2.2 (the metaplectic group as $\mathrm{Sp} \times \mathbb{C}^1$ and the splittings over
  unitary groups).
