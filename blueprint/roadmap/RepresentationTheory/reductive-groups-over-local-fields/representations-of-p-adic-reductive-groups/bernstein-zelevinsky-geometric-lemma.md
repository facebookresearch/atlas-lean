# The Bernstein–Zelevinsky geometric lemma

Let $F$ be a non-archimedean local field, $G = \mathbf{G}(F)$ for a connected reductive group
$\mathbf{G}$ over $F$, with the minimal parabolic subgroup $P_0$, the maximal split torus $A_0$,
the standard Levi subgroups $M < G$ and the functors $i_{G,M}$, $r_{M,G}$ of
[parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md). Let
$W = N_G(A_0)/Z_G(A_0)$ be the Weyl group and $W_M \subseteq W$ the Weyl group of a standard Levi
subgroup $M$. For $w \in W$ fix a representative $\dot w \in N_G(A_0)$ and write
$w(g) = \dot w g \dot w^{-1}$; if $w(M') = N'$, then $w$ also denotes the functor
$\mathrm{Alg}\, M' \to \mathrm{Alg}\, N'$, $(w\rho)(n) = \rho(\dot w^{-1} n \dot w)$, whose
isomorphism class does not depend on the representative. For standard Levi subgroups $M$ and $N$
set

$$W^{M,N} = \{ w \in W \mid w(M \cap P_0) \subseteq P_0,\ w^{-1}(N \cap P_0) \subseteq P_0 \}.$$

1. Each double coset $W_N \backslash W / W_M$ contains exactly one element of $W^{M,N}$. For
   $w \in W^{M,N}$ the groups $M' = M \cap w^{-1}(N)$ and $N' = w(M) \cap N$ are standard Levi
   subgroups of $M$ and of $N$ respectively, and $w(M') = N'$.
2. **Geometric lemma.** For $w \in W^{M,N}$ let
   $F_w = i_{N,N'} \circ w \circ r_{M',M} \colon \mathrm{Alg}\, M \to \mathrm{Alg}\, N$. There is
   an ordering $w_1, \dots, w_k$ of $W^{M,N}$ such that for every smooth representation $\rho$ of
   $M$ the representation $r_{N,G} \circ i_{G,M}(\rho)$ has a filtration
   $0 = \tau_0 \subseteq \tau_1 \subseteq \dots \subseteq \tau_k = r_{N,G} \circ i_{G,M}(\rho)$
   with isomorphisms $\tau_i/\tau_{i-1} \cong F_{w_i}(\rho)$, functorial in $\rho$.

For $G = \mathrm{GL}_n(F)$, $W$ is the symmetric group $S_n$ and, for standard Levi subgroups
attached to ordered partitions $\beta$ and $\gamma$ of $n$, $W^{M,N}$ is the set of permutations
$w$ with $w(k) < w(l)$ whenever $k < l$ lie in the same block of $\beta$, and
$w^{-1}(k) < w^{-1}(l)$ whenever $k < l$ lie in the same block of $\gamma$. Any ordering for which
each union $P_\beta w_1^{-1} P_\gamma \cup \dots \cup P_\beta w_i^{-1} P_\gamma$ ($1 \le i \le k$) is open
in $G$ will do, where $P_\beta$ and $P_\gamma$ are the block upper triangular parabolic subgroups;
in particular one may take $w_k = e$, so that the last subquotient
$\tau_k/\tau_{k-1} \cong i_{N, M \cap N} \circ r_{M \cap N, M}(\rho)$ is a quotient of
$r_{N,G} \circ i_{G,M}(\rho)$.

## Depends on

- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md)
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the Weyl groups $W$ and $W_M$ and the standard Levi subgroups

## Proof depends on

- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the Bruhat decomposition of $G$ into double cosets of standard parabolic subgroups, the filtration of $P_N \backslash G$ by unions of orbits, and $\ell$-sheaves
- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md), for the exactness of the functors
- [The Bernstein–Zelevinsky filtration of a restriction of an induced representation](bernstein-zelevinsky-filtration-theorem.md), for Bernstein and Zelevinsky's Theorem 5.2, of which the geometric lemma is the case of trivial characters (§6.4 there)

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §1.7 (the functors attached to an
  isomorphism), §1.11 (glued objects), §2.6 (Weyl groups), Lemma 2.11 (item 1), §2.12 and the
  Geometrical Lemma (item 2), proved in §§5–6 as a case of Theorem 5.2.
- A. V. Zelevinsky, "Induced representations of reductive p-adic groups. II. On irreducible
  representations of GL(n)", Ann. Sci. École Norm. Sup. (4) 13 (1980), 165–210,
  <http://www.numdam.org/item?id=ASENS_1980_4_13_2_165_0>: Theorem 1.2 (the case of
  $\mathrm{GL}_n$, with the sets $W^{\beta,\gamma}$) and §1.3 with its Corollary (the openness
  condition on the orderings and the choice $w_k = e$, p. 171).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a form of this lemma as `GlobalTheory.Published.GeometricLemma`.
