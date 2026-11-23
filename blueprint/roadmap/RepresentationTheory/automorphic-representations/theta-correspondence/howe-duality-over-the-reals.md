# Howe duality for reductive dual pairs in real symplectic groups

Let $\widetilde{\mathrm{Sp}}$ be the twofold cover of $\mathrm{Sp}_{2N}(\mathbb{R})$ and $\omega$ its
[oscillator representation](metaplectic-group-and-local-weil-representation.md) on a Hilbert space
$\mathcal{Y}$, with space of smooth vectors $\mathcal{Y}^\infty$. Let $(G, G')$ be a reductive dual pair in
$\mathrm{Sp}_{2N}(\mathbb{R})$ and $\tilde G$, $\tilde G'$ the inverse images of $G$ and $G'$ in
$\widetilde{\mathrm{Sp}}$, which commute. For a reductive subgroup $E$ of $\widetilde{\mathrm{Sp}}$ let
$\mathcal{R}(E)$ be the set of infinitesimal equivalence classes of continuous irreducible
[admissible representations](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/admissible-representations-of-real-reductive-groups.md)
of $E$ on locally convex spaces, and $\mathcal{R}(E, \omega) \subset \mathcal{R}(E)$ the classes realized
as quotients of $\mathcal{Y}^\infty$ by $\omega^\infty(E)$-invariant closed subspaces.

1. **Howe duality.** $\mathcal{R}(\tilde G \cdot \tilde G', \omega)$, viewed in
   $\mathcal{R}(\tilde G) \times \mathcal{R}(\tilde G')$ through $\rho \otimes \rho'$, is the graph of a
   bijection between all of $\mathcal{R}(\tilde G, \omega)$ and all of $\mathcal{R}(\tilde G', \omega)$, and
   each $\rho \otimes \rho'$ in it occurs as a quotient of $\mathcal{Y}^\infty$ in a unique way.
2. **Structure of the lift.** For $\rho \in \mathcal{R}(\tilde G, \omega)$, let $\mathcal{N}_\rho$ be the
   intersection of the closed $\tilde G$-invariant subspaces $\mathcal{N}$ of $\mathcal{Y}^\infty$ with
   $\mathcal{Y}^\infty / \mathcal{N} \cong \rho$; then $\mathcal{Y}^\infty / \mathcal{N}_\rho \cong \rho \otimes \rho'_1$
   for a representation $\rho'_1$ of $\tilde G'$ which is finitely generated, admissible and quasisimple
   (the $\mathrm{Ad}$-invariant part of the centre of the enveloping algebra acts by scalars), and has a
   unique irreducible quotient $\rho'$, the one with $\rho \otimes \rho' \in \mathcal{R}(\tilde G \cdot \tilde G', \omega)$.
3. **Algebraic form.** The same holds for the
   [Harish-Chandra modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md):
   on the $(\mathfrak{sp}, \widetilde{\mathrm{U}}(N))$-module $\mathcal{P}$ of the Fock model, for
   $(\mathfrak{g}, \tilde K)$-modules $\rho$ that are quotients of $\mathcal{P}$, the maximal $\rho$-isotypic
   quotient of $\mathcal{P}$ is $\rho \otimes \rho'_1$ with $\rho'_1$ a finitely generated, admissible,
   quasisimple $(\mathfrak{g}', \tilde K')$-module with a unique irreducible quotient $\rho'$, and
   $\rho \mapsto \rho'$ is a bijection.

For unitary dual pairs, $G = \mathrm{U}(p, q)$ and $G' = \mathrm{U}(r, s)$ in $\mathrm{Sp}_{2(p+q)(r+s)}(\mathbb{R})$.

## Depends on

- [Metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md), for the twofold cover of $\mathrm{Sp}_{2N}(\mathbb{R})$, the oscillator representation and its Fock model
- [Admissible representations of real reductive groups](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/admissible-representations-of-real-reductive-groups.md), for continuous admissible representations and smooth vectors
- [Harish-Chandra modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md), for $(\mathfrak{g}, K)$-modules, the correspondence between closed invariant subspaces and submodules, and infinitesimal equivalence

## Proof depends on

- [Duality for compact dual pairs and the (GLₙ, GLₘ)-duality](howe-duality-for-compact-dual-pairs.md), for the structure (3.9) of the Fock space under a compact member of a dual pair, which Howe applies to the maximal compact subgroups and to the auxiliary pairs of products of unitary groups
- [Harish-Chandra modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md), for the passage from item 3 to items 1 and 2 through the density of $K$-finite vectors

## Sources

- R. Howe, "Transcending classical invariant theory", J. Amer. Math. Soc. 2 (1989), 535–552,
  <https://doi.org/10.1090/S0894-0347-1989-0985172-6>: §1, Theorem 1 and Theorem 1A (items 1 and 2),
  and Remark (a); §2, Theorem 2.1 (item 3) and Lemma 2.2 (Theorems 1 and 1A follow from Theorem 2.1);
  §§3–5 (the proof, from Facts 1–3 on dual pairs and the compact case (3.9)); §5, (5.1)–(5.2) (the
  irreducible dual pairs, including $(\mathrm{U}_{p,q}, \mathrm{U}_{r,s}) \subset \mathrm{Sp}_{2(p+q)(r+s)}(\mathbb{R})$).
- W. T. Gan and S. Takeda, "A proof of the Howe duality conjecture", J. Amer. Math. Soc. 29 (2016),
  473–493, arXiv:1407.1995 (version 4): remark (1) after Theorem 1.2 (the study of $K$-types "was used to
  establish the conjecture in the archimedean cases").
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a form for unitary dual pairs over the archimedean places of a CM extension, in the Fock model,
  as `GlobalTheory.Published.HoweDualityReal`.
