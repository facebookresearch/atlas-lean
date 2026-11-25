# Uniqueness of cuspidal support

Let $F$ be a non-archimedean local field and $G = \mathbf{G}(F)$ for a connected reductive group
$\mathbf{G}$ over $F$, with the minimal parabolic subgroup $P_0$, the maximal split torus $A_0$, the
standard Levi subgroups $M < G$ and the functors $i_{G,M}$ of
[parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md). Let
$W = N_G(A_0)/Z_G(A_0)$ be the Weyl group and $W_M$ that of $M$; for $w \in W$ with representative
$\dot w \in N_G(A_0)$ write $w(M) = \dot w M \dot w^{-1}$, and for a representation $\rho$ of $M$ let
$w(\rho)$ be the representation $m' \mapsto \rho(\dot w^{-1} m' \dot w)$ of $w(M)$. For standard Levi
subgroups $M$ and $N$ let $W(M, N) = \{ w \in W \mid w(M) = N \}$. Then $M$ and $N$ are
**associate** if $W(M, N) \ne \emptyset$, and representations $\rho$ of $M$ and $\rho'$ of $N$ are
associate if $\rho' \cong w(\rho)$ for some $w \in W(M, N)$.

**Theorem (Bernstein–Zelevinsky).** Let $M$ and $N$ be standard Levi subgroups, $\rho$ and $\rho'$
irreducible [cuspidal](cuspidal-representations-and-jacquet-embedding.md) representations of $M$
and $N$, $\pi = i_{G,M}(\rho)$ and $\pi' = i_{G,N}(\rho')$. The following are equivalent:

1. $M$ and $N$ are associate, and $\rho$ and $\rho'$ are associate;
2. $\mathrm{Hom}_G(\pi, \pi') \ne 0$;
3. $\pi$ and $\pi'$ have the same irreducible subquotients, with the same multiplicities in their
   composition series;
4. $\pi$ and $\pi'$ have an irreducible subquotient in common.

Moreover $\dim \mathrm{Hom}_G(\pi, \pi') \le \lvert W(\rho, \rho')/W_M \rvert$, where
$W(\rho, \rho') = \{ w \in W(M, N) \mid w(\rho) \cong \rho' \}$.

So the **cuspidal support** of an irreducible smooth representation $\omega$ of $G$, a pair
$(M, \rho)$ with $\rho$ an irreducible cuspidal representation of a standard Levi subgroup $M$ such
that $\omega$ is a subquotient of $i_{G,M}(\rho)$ (it exists by Jacquet's embedding theorem), is
unique up to association. For $G = \mathrm{GL}_n(F)$, writing $\rho_1 \times \dots \times \rho_r$
for the representation of $\mathrm{GL}_n(F)$ induced from $\rho_1 \otimes \dots \otimes \rho_r$ on
the block-diagonal Levi subgroup $\mathrm{GL}_{n_1}(F) \times \dots \times \mathrm{GL}_{n_r}(F)$,
this reads: there are irreducible cuspidal representations $\rho_i$ of groups
$\mathrm{GL}_{n_i}(F)$, $n_1 + \dots + n_r = n$, such that $\omega$ is a subquotient of
$\rho_1 \times \dots \times \rho_r$; the multiset $\{\rho_1, \dots, \rho_r\}$, the **support** of
$\omega$, is determined by $\omega$; and for some ordering $\omega$ embeds in
$\rho_{i_1} \times \dots \times \rho_{i_r}$.

## Depends on

- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md)
- [Cuspidal representations and Jacquet's embedding theorem](cuspidal-representations-and-jacquet-embedding.md), for cuspidal representations and the existence of the cuspidal support
- [Finite length of parabolically induced representations](finite-length-of-induced-representations.md), for the composition series of $\pi$ and $\pi'$
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for standard Levi subgroups and the Weyl groups $W$ and $W_M$

## Proof depends on

- [The Bernstein–Zelevinsky geometric lemma](bernstein-zelevinsky-geometric-lemma.md), with its corollary on the Jacquet modules of representations induced from cuspidal ones
- [Finite length of parabolically induced representations](finite-length-of-induced-representations.md), for the first step of the proof of finite length, which constrains the cuspidal data of the subquotients
- [Cuspidal representations and Jacquet's embedding theorem](cuspidal-representations-and-jacquet-embedding.md), for the fact that a cuspidal subquotient of an admissible representation is a quotient of it
- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md), for exactness, Frobenius reciprocity and transitivity
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the chains of elementary maps linking associate standard Levi subgroups

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §1.7 (the functor attached to an
  isomorphism), §2.6 (associate standard Levi subgroups and representations), §2.7 (the example of
  $\mathrm{GL}_n$), Theorem 2.9 (this statement, with part (b) the bound on $\dim \mathrm{Hom}$),
  proved in §§2.15–2.16 from Proposition 2.3, Theorem 2.4 (b), Corollary 2.13, step (1) of §2.14
  and Lemma 2.17.
- A. V. Zelevinsky, "Induced representations of reductive p-adic groups. II. On irreducible
  representations of GL(n)", Ann. Sci. École Norm. Sup. (4) 13 (1980), 165–210,
  <http://www.numdam.org/item?id=ASENS_1980_4_13_2_165_0>: §1.10, Proposition (the support of an
  irreducible representation of $\mathrm{GL}_n$, "determined by $\omega$", and the embedding for
  some ordering, citing Bernstein–Zelevinsky 1977, 2.5 and 2.9).
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): (2.2.3)–(2.2.4) (the supercuspidal support).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  proves the uniqueness of the support for $\mathrm{GL}_n$ from
  forms of the geometric lemma and of the Bernstein–Zelevinsky finiteness theorems
  (`GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique`).
