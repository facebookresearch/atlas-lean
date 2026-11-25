# Finite length of parabolically induced representations

Let $F$ be a non-archimedean local field, $G = \mathbf{G}(F)$ for a connected reductive group
$\mathbf{G}$ over $F$, with the standard Levi subgroups $M < G$, the Weyl group $W$ and the
functors $i_{G,M}$, $r_{M,G}$ of
[parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md). For a
standard Levi subgroup $M$ let $W(M, *) = \{ w \in W \mid w(M) \text{ is a standard Levi subgroup} \}$
and let $l(M)$ be the number of cosets in $W(M,*)/W_M$; for
$M = \mathrm{GL}_{n_1}(F) \times \dots \times \mathrm{GL}_{n_r}(F)$ in $\mathrm{GL}_n(F)$,
$l(M) = r!$.

1. If $\rho$ is an irreducible cuspidal representation of a standard Levi subgroup $M$, then
   $i_{G,M}(\rho)$ has finite length, at most $l(M)$.
2. The functors $i_{G,M}$ and $r_{M,G}$ carry representations of finite length to representations
   of finite length.
3. Every finitely generated admissible representation of $G$ has finite length.

Representations of finite length are admissible, because irreducible representations are
([Jacquet's embedding theorem](cuspidal-representations-and-jacquet-embedding.md)) and an extension
of admissible representations is admissible. For $r_{M,G}$, item 2 follows from item 3 applied
to $M$, since the Jacquet module of a finitely generated admissible representation is finitely
generated and admissible.

## Depends on

- [Smooth and admissible representations of p-adic groups](smooth-representations-of-p-adic-groups.md)
- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md)
- [Cuspidal representations and Jacquet's embedding theorem](cuspidal-representations-and-jacquet-embedding.md), for cuspidal representations
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the Weyl group and its action on standard Levi subgroups

## Proof depends on

- [The Bernstein–Zelevinsky geometric lemma](bernstein-zelevinsky-geometric-lemma.md)
- [Cuspidal representations and Jacquet's embedding theorem](cuspidal-representations-and-jacquet-embedding.md), for the embedding theorem and the admissibility of irreducible representations
- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md), for exactness, Frobenius reciprocity and the finite generation and admissibility of Jacquet modules

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §2.8 and Theorem 2.8 (item 1, with the
  example $l(M) = r!$), proved in §2.14 from Proposition 2.3 and Corollary 2.13 of the Geometrical
  Lemma 2.12.
- A. V. Zelevinsky, "Induced representations of reductive p-adic groups. II. On irreducible
  representations of GL(n)", Ann. Sci. École Norm. Sup. (4) 13 (1980), 165–210,
  <http://www.numdam.org/item?id=ASENS_1980_4_13_2_165_0>: Proposition 1.4 (item 2 for
  $\mathrm{GL}_n$, proved from Bernstein–Zelevinsky 1977, 2.5, 2.8 and 2.12).
- W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, notes, draft of 1 May 1995, <https://personal.math.ubc.ca/~cass/research/pdf/p-adic-book.pdf>:
  §2.1 (admissibility of extensions), Theorem 3.3.1, Corollary 6.3.7, the Corollary of the
  Corollary 6.3.8 (induction of admissible representations of finite length) and Theorem 6.3.10
  (item 3).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a form of item 2 for $\mathrm{GL}_n$ as `GlobalTheory.Published.BernsteinZelevinskyFiniteness`.
