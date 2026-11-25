# Howe duality for reductive dual pairs in real symplectic groups

Let $\widetilde{\mathrm{Sp}}$ be the twofold cover of $\mathrm{Sp}_{2N}(\mathbb{R})$ and $\omega$ its
[oscillator representation](metaplectic-group-and-local-weil-representation.md) on a Hilbert space
$\mathcal{Y}$, with space of smooth vectors $\mathcal{Y}^\infty$. Let $(G, G')$ be a reductive dual pair in
$\mathrm{Sp}_{2N}(\mathbb{R})$, $\tilde G$ and $\tilde G'$ the inverse images of $G$ and $G'$ in
$\widetilde{\mathrm{Sp}}$, which commute, and $K$, $K'$ maximal compact subgroups of $G$, $G'$ compatible
with a Cartan decomposition of $\mathfrak{sp}$, with inverse images $\tilde K$, $\tilde K'$.

For a reductive subgroup $E$ of $\widetilde{\mathrm{Sp}}$ let $\mathcal{R}(E)$ be the set of infinitesimal
equivalence classes of continuous irreducible
[admissible representations](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/admissible-representations-of-real-reductive-groups.md)
of $E$ on locally convex spaces, and $\mathcal{R}(E, \omega) \subset \mathcal{R}(E)$ the classes realized as
quotients of $\mathcal{Y}^\infty$ by closed $\omega^\infty(E)$-invariant subspaces. Classes of $\tilde G \times \tilde G'$
are identified with pairs $(\rho, \rho')$ through $\rho \otimes \rho'$, defined up to infinitesimal equivalence.
On the algebraic side let $\mathcal{P} \subset \mathcal{Y}^\infty$ be the $(\mathfrak{sp}, \tilde{\mathrm U}(N))$-module of
$\tilde{\mathrm U}(N)$-finite vectors (the polynomials of the Fock model), and $\mathcal{R}(\mathfrak{g}, \tilde K, \omega)$
the set of isomorphism classes of **irreducible** $(\mathfrak{g}, \tilde K)$-modules isomorphic to a quotient
$\mathcal{P} / \mathcal{N}$ by a $(\mathfrak{g}, \tilde K)$-submodule. A representation of a possibly disconnected member $E$ (or of
its Lie algebra and maximal compact subgroup) is **quasisimple** if the subalgebra
$\mathcal{Z}(\mathfrak{e}_{\mathbb{C}})^{\mathrm{Ad}\, E}$ of the centre of the enveloping algebra fixed by the adjoint action of $E$ (not only of
its identity component) acts by scalars (Howe, Transcending, p. 536); for connected $E$, such as a unitary group,
this is the whole centre.

1. **Algebraic Howe duality** (Howe, Theorem 2.1). For $\rho \in \mathcal{R}(\mathfrak{g}, \tilde K, \omega)$ let
   $\mathcal{N}_\rho$ be the intersection of the submodules $\mathcal{N}$ with $\mathcal{P}/\mathcal{N} \cong \rho$. Then
   $\mathcal{P}/\mathcal{N}_\rho \cong \rho \otimes \rho'_1$ for a $(\mathfrak{g}', \tilde K')$-module $\rho'_1$ which is finitely
   generated, admissible and quasisimple, and has a unique irreducible quotient $\rho'$; and $\rho \mapsto \rho'$ is
   a bijection from $\mathcal{R}(\mathfrak{g}, \tilde K, \omega)$ onto $\mathcal{R}(\mathfrak{g}', \tilde K', \omega)$.
2. **Smooth Howe duality** (Howe, Theorems 1 and 1A). The subset $\mathcal{R}(\tilde G \cdot \tilde G', \omega)$ of
   $\mathcal{R}(\tilde G) \times \mathcal{R}(\tilde G')$ is the graph of a bijection between $\mathcal{R}(\tilde G, \omega)$ and
   $\mathcal{R}(\tilde G', \omega)$, and for each $\rho \otimes \rho'$ in it the closed $\tilde G \cdot \tilde G'$-invariant
   subspace of $\mathcal{Y}^\infty$ with quotient in the class of $\rho \otimes \rho'$ is unique. For
   $\rho \in \mathcal{R}(\tilde G, \omega)$, the quotient of $\mathcal{Y}^\infty$ by the intersection of the closed
   $\tilde G$-invariant subspaces with quotient in the class of $\rho$ is a representation of $\tilde G \cdot \tilde G'$ of
   the form $\rho \otimes \rho'_1$, up to infinitesimal equivalence, with $\rho'_1$ finitely generated (its $\tilde K'$-finite
   vectors generate a finitely generated module over the enveloping algebra), admissible and quasisimple, and
   with a unique irreducible quotient $\rho'$, the partner of $\rho$.
3. **Compatibility.** The $\tilde K$-finite vectors of a class in $\mathcal{R}(\tilde G, \omega)$ form a module in
   $\mathcal{R}(\mathfrak{g}, \tilde K, \omega)$, and the smooth correspondence of item 2 induces on these the algebraic
   correspondence of item 1.

For unitary dual pairs, $G = \mathrm{U}(p, q)$ and $G' = \mathrm{U}(r, s)$ in $\mathrm{Sp}_{2(p+q)(r+s)}(\mathbb{R})$.

## Depends on

- [Metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md), for the twofold cover of $\mathrm{Sp}_{2N}(\mathbb{R})$, the oscillator representation and its Fock model
- [Admissible representations of real reductive groups](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/admissible-representations-of-real-reductive-groups.md), for continuous admissible representations and smooth vectors
- [Harish-Chandra modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md), for $(\mathfrak{g}, K)$-modules, the correspondence between closed invariant subspaces and submodules, and infinitesimal equivalence

## Proof depends on

- [Duality for compact dual pairs in the Fock model](howe-duality-for-compact-dual-pairs.md), for the structure (3.9) of the Fock space under a compact member of a dual pair, which Howe applies to the maximal compact subgroups and to the auxiliary pairs of products of unitary groups in §§3–5 to prove item 1
- [Harish-Chandra modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md), for the passage from item 1 to items 2 and 3 (Howe's Lemma 2.2): starting from a class that occurs as a smooth quotient, the image of $\mathcal{P}$ is dense and its $\tilde K$-isotypic components are finite-dimensional, so its $\tilde K$-finite vectors are an algebraic quotient of $\mathcal{P}$; the argument does not show that every algebraic quotient occurs smoothly
- [Classical invariant theory and harmonics](classical-invariant-theory-and-harmonics.md), for the correspondence of the $\mathrm{Ad}$-invariant centres $\mathcal{Z}(\mathfrak{g})^{\mathrm{Ad}\, \tilde G}$ and $\mathcal{Z}(\mathfrak{g}')^{\mathrm{Ad}\, \tilde G'}$ (Howe, Remarks, §5 (a)): since $\rho$ is irreducible and admissible, $\mathcal{Z}(\mathfrak{g})^{\mathrm{Ad}\, \tilde G}$ acts on it by scalars, so $\mathcal{Z}(\mathfrak{g}')^{\mathrm{Ad}\, \tilde G'}$ acts on $\rho'_1$ by scalars determined by them and $\rho'_1$ is quasisimple; and Harish-Chandra's theorem that a finitely generated quasisimple $(\mathfrak{g}', \tilde K')$-module is admissible; these are the two steps by which Howe (Transcending, p. 547) obtains the admissibility of the algebraic lift in item 1

## Sources

- R. Howe, "Transcending classical invariant theory", J. Amer. Math. Soc. 2 (1989), 535–552,
  <https://doi.org/10.1090/S0894-0347-1989-0985172-6>: §1, the definitions of $\mathcal{R}(E)$ and
  $\mathcal{R}(E, \omega)$ ("infinitesimal equivalence classes of continuous irreducible admissible
  representations"), Theorem 1 and Theorem 1A (item 2), (1.1) and Remark (a); §2, (2.1)–(2.5), the
  definition of $\mathcal{R}(\mathfrak{g}, \tilde K, \omega)$ as classes of irreducible modules realized as quotients,
  Theorem 2.1 (item 1) and Lemma 2.2 with its proof (item 3, and Theorems 1 and 1A from Theorem 2.1);
  §§3–5 (the proof of Theorem 2.1, from Facts 1–3 on dual pairs and the compact case (3.9)); §5,
  (5.1)–(5.2) (the irreducible dual pairs, including
  $(\mathrm{U}_{p,q}, \mathrm{U}_{r,s}) \subset \mathrm{Sp}_{2(p+q)(r+s)}(\mathbb{R})$).
- W. T. Gan and S. Takeda, "A proof of the Howe duality conjecture", J. Amer. Math. Soc. 29 (2016),
  473–493, arXiv:1407.1995 (version 4): remark (1) after Theorem 1.2 (the study of $K$-types "was used to
  establish the conjecture in the archimedean cases").
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a specialized analogue, for unitary dual pairs at the archimedean places of a CM extension in the
  polynomial Fock model (a bound on chains of theta submodules and a unique-quotient property), as
  `GlobalTheory.Published.HoweDualityReal`.
