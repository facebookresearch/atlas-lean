# Depth under parabolic induction and Jacquet functors

Let $k$ be a non-archimedean local field, $\mathbf{G}$ a connected reductive group over $k$ and
$\mathcal{G} = \mathbf{G}(k)$, and let $\varrho$ denote the depth of irreducible admissible
representations, defined for $\mathcal{G}$ and for the groups of $k$-points of its Levi subgroups
in [depth and unrefined minimal K-types](depth-and-unrefined-minimal-k-types.md). Let
$\mathcal{P} = \mathcal{M}\mathcal{N}$ be the group of $k$-points of a parabolic $k$-subgroup
$P = MN$ of $\mathbf{G}$ with Levi subgroup $M$ and unipotent radical $N$, let
$J_{\mathcal{N}}(V)$ be the space of $\mathcal{N}$-coinvariants of a smooth representation $V$ of
$\mathcal{G}$, a representation of $\mathcal{M}$, and let $\mathrm{Ind}_{\mathcal{M}\mathcal{N}}^{\mathcal{G}}$
be unnormalized smooth induction. Twisting a representation of $\mathcal{M}$ by the positive
character $\delta_{\mathcal{P}}^{1/2}$ does not change its depth, since that character is trivial on
the compact subgroups $\mathcal{M}_{x,r}$, so the same statements hold for the normalized functors
$r_{M,G}$ and $i_{G,M}$ of
[parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md).

**Theorem (Moy–Prasad).**

1. Let $\pi$ be an irreducible admissible representation of $\mathcal{G}$ with
   $J_{\mathcal{N}}(\pi) \ne 0$. Then every irreducible subquotient $\sigma$ of the
   $\mathcal{M}$-module $J_{\mathcal{N}}(\pi)$ satisfies $\varrho(\sigma) = \varrho(\pi)$.
2. Let $\sigma$ be an irreducible admissible representation of $\mathcal{M}$ and $\pi$ an
   irreducible subquotient of $\mathrm{Ind}_{\mathcal{M}\mathcal{N}}^{\mathcal{G}}\, \sigma$. Then
   $\varrho(\pi) = \varrho(\sigma)$.

Moy and Prasad deduce item 2 from item 1 by replacing $\mathcal{P}$ by an associate parabolic
subgroup for which $\pi$ is a subrepresentation, through their Theorem 2.5, which is stated for
absolutely cuspidal inducing representations. For unnormalized induction from an arbitrary
$\sigma$ that step is not available: for $\mathrm{GL}_2$, unnormalized induction of the trivial
character from either Borel subgroup has the trivial character as its only irreducible
subrepresentation and the Steinberg representation as a quotient. Item 2 follows from item 1
through normalized cuspidal supports. The representation $\sigma\delta_{\mathcal{P}}^{-1/2}$ embeds
in $i_{M,L}(\rho)$ for an irreducible cuspidal representation $\rho$ of a Levi subgroup $L$ of $M$,
so $\rho$ is a quotient of a normalized Jacquet module of $\sigma\delta_{\mathcal{P}}^{-1/2}$ and
$\varrho(\rho) = \varrho(\sigma)$ by item 1. By exactness and transitivity of induction, $\pi$ is a
subquotient of $i_{G,L}(\rho)$; by Jacquet's embedding theorem and the uniqueness of cuspidal
support, $\pi$ embeds in $i_{G,L'}(\rho')$ for a pair $(L', \rho')$ conjugate to $(L, \rho)$, so
$\rho'$ is a quotient of a normalized Jacquet module of $\pi$, and item 1 gives
$\varrho(\pi) = \varrho(\rho') = \varrho(\rho)$, depth being invariant under conjugation.

In particular, if $(M, \rho)$ is a cuspidal support of an irreducible representation $\pi$, as in
[uniqueness of cuspidal support](uniqueness-of-cuspidal-support.md), then
$\varrho(\rho) = \varrho(\pi)$ by item 2. For $\mathcal{G} = \mathrm{GL}_n(k)$ and $\pi$ a
subquotient of $\rho_1 \times \dots \times \rho_r$ with $\rho_a$ irreducible cuspidal representations
of groups $\mathrm{GL}_{n_a}(k)$, the filtration subgroups of the block-diagonal Levi subgroup are
the products of those of its factors, so every $\rho_a$ has depth at most $\varrho(\pi)$, and if
$\pi$ has depth zero then so does every $\rho_a$. As the principal congruence subgroup
$K_1 = \ker(\mathrm{GL}_m(\mathcal{O}_k) \to \mathrm{GL}_m(\mathfrak{f}))$ of $\mathrm{GL}_m(k)$ is the
subgroup $\mathcal{G}_{x,0+}$ at every point $x$ of the building lying over the vertex of the
reduced building given by the homothety class of the lattice $\mathcal{O}_k^m$ (the filtration does
not depend on the central coordinate), and every $\mathcal{G}_{y,0+}$ contains a
$\mathrm{GL}_m(k)$-conjugate of it, an irreducible representation of
$\mathrm{GL}_m(k)$ has depth zero exactly when it has nonzero $K_1$-fixed vectors. So if $\pi$ has
nonzero $K_1$-fixed vectors, so does every member $\rho_a$ of its support.

## Depends on

- [Depth and unrefined minimal K-types](depth-and-unrefined-minimal-k-types.md), for the depth of irreducible admissible representations of $\mathcal{G}$ and of $\mathcal{M}$
- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md), for Jacquet modules and parabolic induction
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for parabolic subgroups and their Levi decompositions, and for the filtrations of products and of $\mathrm{GL}_m$ used in the last paragraph
- [Uniqueness of cuspidal support](uniqueness-of-cuspidal-support.md), for cuspidal supports, in the last paragraph

## Proof depends on

- [Depth and unrefined minimal K-types](depth-and-unrefined-minimal-k-types.md), for the existence of unrefined minimal K-types and their associativity
- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md), for Jacquet's surjectivity theorem applied to the subgroups $\mathcal{G}_{x,r}$, $r > 0$, with $x$ in the apartment of a maximal $k$-split torus of $\mathbf{G}$ contained in $M$, where they have an Iwahori decomposition with respect to $\mathcal{P}$ and $\mathcal{M}$, and for Frobenius reciprocity, exactness and transitivity of induction in the proof of item 2
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the Iwahori decomposition of $\mathcal{G}_{x,r}$, $r > 0$, and the identification of $\mathcal{M}_{x,r} = \mathcal{M} \cap \mathcal{G}_{x,r}$ with the filtration subgroups of $\mathcal{M}$, both for $x$ in the apartment of a maximal $k$-split torus contained in $M$ (Moy–Prasad 4.2 and §4.3), for the nilpotent cosets used in the proof of Moy–Prasad's Proposition 4.7, and for the conjugation invariance of the filtrations, hence of depth
- [Uniqueness of cuspidal support](uniqueness-of-cuspidal-support.md), for the conjugacy of the cuspidal data $(L, \rho)$ and $(L', \rho')$ of $\pi$ in the proof of item 2 by normalized cuspidal supports
- [Cuspidal representations and Jacquet's embedding theorem](cuspidal-representations-and-jacquet-embedding.md), for the embeddings of $\sigma\delta_{\mathcal{P}}^{-1/2}$ and of $\pi$ into representations induced from cuspidal ones, in the proof of item 2

## Sources

- A. Moy and G. Prasad, "Jacquet functors and unrefined minimal K-types", Comment. Math. Helv. 71
  (1996), 98–121, <https://doi.org/10.5169/seals-53837>: §2 (Theorem 2.2, Jacquet's surjectivity;
  §2.3, Frobenius reciprocity for unnormalized induction; Theorem 2.5, induced representations
  from associate parabolic subgroups, for absolutely cuspidal inducing representations), §§4.1–4.4
  (setting; Theorem 4.2: "For $S \subset M$, any point $x \in A(S)$ and any $r > 0$, the filtration
  subgroup $\mathcal{G}_{x,r}$ of the parahoric subgroup $\mathcal{G}_x$ has the Iwahori decomposition
  with respect to $\mathcal{P}$ and the Levi factor $\mathcal{M}$"; §4.3, $\mathcal{M}_{x,r}$ for
  $x \in A(S)$), Theorem 4.5 (item 1: "In particular $\varrho(\sigma) = \varrho(\pi)$ for any
  irreducible subquotient $\sigma$ of $J_{\mathcal{N}}(V_\pi)$") and Theorem 5.2 (1) (item 2; its
  printed proof begins "By Theorem 2.5, after replacing the inducing parabolic $\mathcal{P}$ by a
  suitable $\mathcal{M}$-associate").
- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §1.7 ("any positive character of a
  compact $l$-group equals 1").
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the consequence of the last paragraph, for $\mathrm{GL}_n$ and the principal congruence
  subgroups, as `GlobalTheory.Published.DepthZeroSupport`.
