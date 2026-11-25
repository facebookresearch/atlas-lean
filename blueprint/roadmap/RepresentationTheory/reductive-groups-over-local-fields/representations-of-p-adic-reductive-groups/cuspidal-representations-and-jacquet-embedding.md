# Cuspidal representations and Jacquet's embedding theorem

Let $F$ be a non-archimedean local field, $G = \mathbf{G}(F)$ for a connected reductive group
$\mathbf{G}$ over $F$ with centre $Z$, and use the standard Levi subgroups $M < G$ and the
functors $i_{G,M}$, $r_{M,G}$ of
[parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md). A smooth
representation $\pi$ of $G$ is **quasicuspidal** if $r_{M,G}(\pi) = 0$ for every standard Levi
subgroup $M \ne G$, and **cuspidal** if it is admissible and quasicuspidal. Casselman calls the
cuspidal representations absolutely cuspidal, and Harish-Chandra supercuspidal.

1. **Matrix coefficients.** For an admissible representation $\pi$ of $G$ the following are
   equivalent: $\pi$ is cuspidal; $\tilde\pi$ is cuspidal; every matrix coefficient of $\pi$ has
   compact support modulo $Z$ (the forward implication is due to Jacquet).
2. **Jacquet's embedding theorem.** Every irreducible smooth representation $\omega$ of $G$
   embeds in $i_{G,M}(\rho)$ for some standard Levi subgroup $M$ and some irreducible cuspidal
   representation $\rho$ of $M$. In particular every irreducible smooth representation of $G$ is
   admissible.
3. **Cuspidal parts split off.** Every smooth representation $\pi$ of $G$ decomposes as
   $\pi = \pi_c \oplus \pi_n$ with $\pi_c$ quasicuspidal and $\pi_n$ without nonzero quasicuspidal
   subquotients. If $\pi$ is admissible and has an irreducible cuspidal subquotient $\omega$, then
   $\pi$ has a subrepresentation and a quotient isomorphic to $\omega$. If $M \ne G$ and $\rho$ is a
   smooth representation of $M$, then $i_{G,M}(\rho)_c = 0$.

For $G = \mathrm{GL}_n(F)$, by (1), (2) and a theorem of Harish-Chandra, an irreducible
representation is cuspidal if and only if it is not a subquotient of a representation
parabolically induced from an admissible representation of a proper standard Levi subgroup;
Wedhorn takes this as the definition of supercuspidal representations.

## Depends on

- [Smooth and admissible representations of p-adic groups](smooth-representations-of-p-adic-groups.md)
- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md)

## Proof depends on

- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md), for exactness, Frobenius reciprocity and the finite generation and admissibility of Jacquet modules
- [Jacquet modules and the asymptotics of matrix coefficients](asymptotics-of-matrix-coefficients.md), for Jacquet's lemmas, which give the equivalence with compactly supported matrix coefficients, and for the compactly supported matrix coefficients through which the quasicuspidal part of a smooth representation splits off as a direct summand (item 3; a cuspidal constituent need not split off, only occur as a subrepresentation and a quotient)

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §2.4 (quasicuspidal and cuspidal
  representations), Theorem 2.4 (a), (b) and (d) (item 3; "Parts (a)-(c) in the case
  $G = \mathrm{GL}(n, F)$ are proved in [1], chap. II; in the general case proofs are similar") and
  Theorem 2.5 ("Let $\omega \in \mathrm{Irr}\, G$. Then there exists a
  subgroup $M < G$ and a cuspidal representation $\rho \in \mathrm{Irr}\, M$ such that $\omega$ can
  be embedded into $i_{G,M}(\rho)$; in particular, $\omega$ is admissible"), whose proof is
  referred there to H. Jacquet, C. R. Acad. Sci. Paris 280 (1975), 1271–1272, and, for
  $\mathrm{GL}_n$, to Bernstein–Zelevinsky, Uspekhi Mat. Nauk 31 (1976), chap. II.
- W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, notes, draft of 1 May 1995, <https://personal.math.ubc.ca/~cass/research/pdf/p-adic-book.pdf>:
  §5.1 (absolutely cuspidal, or supercuspidal, representations) and Theorem 5.1.2 (Jacquet's
  embedding theorem for irreducible admissible representations), Theorem 5.2.1 (Jacquet: compact
  support modulo the centre), Theorem 5.3.1 (the three equivalent conditions) and Theorem 5.4.1
  (absolutely cuspidal $\omega$-representations are projective and injective among smooth
  $\omega$-representations).
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): Definition (2.2.2) (supercuspidal representations of
  $\mathrm{GL}_n(K)$) and Theorem (2.2.7) (equivalence with compact support of matrix coefficients
  modulo the centre, a theorem of Harish-Chandra).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the admissibility of irreducible representations of $\mathrm{GL}_n$ as
  `GlobalTheory.Published.IrreducibleAdmissibleGL`.
