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

In particular, if $(M, \rho)$ is a cuspidal support of an irreducible representation $\pi$, as in
[uniqueness of cuspidal support](uniqueness-of-cuspidal-support.md), then
$\varrho(\rho) = \varrho(\pi)$ by item 2. For $\mathcal{G} = \mathrm{GL}_n(k)$ and $\pi$ a
subquotient of $\rho_1 \times \dots \times \rho_r$ with $\rho_a$ irreducible cuspidal representations
of groups $\mathrm{GL}_{n_a}(k)$, the filtration subgroups of the block-diagonal Levi subgroup are
the products of those of its factors, so every $\rho_a$ has depth at most $\varrho(\pi)$, and if
$\pi$ has depth zero then so does every $\rho_a$. As the principal congruence subgroup
$K_1 = \ker(\mathrm{GL}_m(\mathcal{O}_k) \to \mathrm{GL}_m(\mathfrak{f}))$ of $\mathrm{GL}_m(k)$ is the
subgroup $\mathcal{G}_{x,0+}$ at the vertex $x$ of the lattice $\mathcal{O}_k^m$, and every
$\mathcal{G}_{y,0+}$ contains a $\mathrm{GL}_m(k)$-conjugate of it, an irreducible representation of
$\mathrm{GL}_m(k)$ has depth zero exactly when it has nonzero $K_1$-fixed vectors. So if $\pi$ has
nonzero $K_1$-fixed vectors, so does every member $\rho_a$ of its support.

## Depends on

- [Depth and unrefined minimal K-types](depth-and-unrefined-minimal-k-types.md), for the depth of irreducible admissible representations of $\mathcal{G}$ and of $\mathcal{M}$
- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md), for Jacquet modules and parabolic induction
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for parabolic subgroups and their Levi decompositions, and for the filtrations of products and of $\mathrm{GL}_m$ used in the last paragraph
- [Uniqueness of cuspidal support](uniqueness-of-cuspidal-support.md), for cuspidal supports, in the last paragraph

## Proof depends on

- [Depth and unrefined minimal K-types](depth-and-unrefined-minimal-k-types.md), for the existence of unrefined minimal K-types and their associativity
- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md), for Jacquet's surjectivity theorem applied to the subgroups $\mathcal{G}_{x,r}$, which have an Iwahori decomposition with respect to $\mathcal{P}$ and $\mathcal{M}$ for $r > 0$, and for Frobenius reciprocity
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the Iwahori decomposition of the $\mathcal{G}_{x,r}$, the identification of $\mathcal{M}_{x,r}$ with the filtration subgroups of $\mathcal{M}$ and the nilpotent cosets used in the proof of Moy–Prasad's Proposition 4.7
- [Uniqueness of cuspidal support](uniqueness-of-cuspidal-support.md), for the replacement of the inducing parabolic subgroup by an associate one in the proof of item 2
- [Cuspidal representations and Jacquet's embedding theorem](cuspidal-representations-and-jacquet-embedding.md), for the embedding of an irreducible subquotient into a representation induced from a cuspidal one

## Sources

- A. Moy and G. Prasad, "Jacquet functors and unrefined minimal K-types", Comment. Math. Helv. 71
  (1996), 98–121, <https://doi.org/10.5169/seals-53837>: §2 (Theorem 2.2, Jacquet's surjectivity;
  §2.3, Frobenius reciprocity for unnormalized induction; Theorem 2.5, induced representations
  from associate parabolic subgroups), §§4.1–4.4 (setting, Theorem 4.2 on the Iwahori
  decomposition of $\mathcal{G}_{x,r}$), Theorem 4.5 (item 1: "In particular
  $\varrho(\sigma) = \varrho(\pi)$ for any irreducible subquotient $\sigma$ of $J_{\mathcal{N}}(V_\pi)$")
  and Theorem 5.2 (1) (item 2), with Lemma 5.1 and the proof of Theorem 5.2.
- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §1.7 ("any positive character of a
  compact $l$-group equals 1").
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the consequence of the last paragraph, for $\mathrm{GL}_n$ and the principal congruence
  subgroups, as `GlobalTheory.Published.DepthZeroSupport`.
