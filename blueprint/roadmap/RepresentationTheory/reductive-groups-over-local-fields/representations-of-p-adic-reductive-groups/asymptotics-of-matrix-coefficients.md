# Jacquet modules and the asymptotics of matrix coefficients

This node is still to be broken down. It covers the asymptotic analysis of matrix coefficients of
admissible representations of $G = \mathbf{G}(F)$, for a connected reductive group $\mathbf{G}$
over a non-archimedean local field $F$, through Jacquet modules. The proofs of the following
statements about [smooth representations](smooth-representations-of-p-adic-groups.md) use it: the
characterization of
[cuspidal representations](cuspidal-representations-and-jacquet-embedding.md) by compactly
supported matrix coefficients, the
[Borel–Casselman theorem](borel-casselman-theorem.md), and the
[square-integrable](../representations-of-p-adic-gl-n/essentially-square-integrable-representations-of-gl-n.md),
[tempered](../representations-of-p-adic-gl-n/tempered-and-unitary-representations-of-gl-n.md) and
[Langlands](../representations-of-p-adic-gl-n/langlands-classification-for-gl-n.md) classifications for $\mathrm{GL}_n$.

- Jacquet's first and second lemmas on vectors fixed by compact open subgroups with an Iwahori
  factorization and on the action of the elements of $A^-$, and the canonical non-degenerate
  pairing between the Jacquet modules $V_N$ and $\tilde V_{\bar N}$ for opposite parabolic
  subgroups.
- The asymptotic expansion of matrix coefficients on $A^-$ in terms of Jacquet modules, the
  central characters (exponents) of Jacquet modules, and the compact support modulo the centre of
  the matrix coefficients of cuspidal representations.
- Casselman's criterion: an admissible representation with central character $\omega$ is
  square-integrable modulo the centre if and only if $\omega$ is unitary and the exponents of its
  Jacquet modules satisfy strict inequalities on the cones $A^-_\Theta$; the analogous criterion
  for tempered representations.
- Langlands's classification of irreducible admissible representations by tempered
  representations of Levi subgroups and exponents, for p-adic groups.

A good expansion has statement pages for Jacquet's lemmas, the canonical pairing, the asymptotic
expansion, Casselman's square-integrability and temperedness criteria and the Langlands
classification, each citing the sources below with locators.

## Depends on

- [Smooth and admissible representations of p-adic groups](smooth-representations-of-p-adic-groups.md)
- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md)
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for Iwahori factorizations and the cones $A^-_\Theta$

## Proof depends on

- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the compact open subgroups with an Iwahori factorization in Jacquet's lemmas and for the cones $A^-_\Theta$
- Not yet a page: Casselman's Proposition 1.4.6 (p. 15): there is an open subgroup $\Gamma$ of $G$, compact modulo the centre and containing $A_\emptyset(\mathcal{O})$, with $G = \Gamma A_\emptyset^- \Gamma$; the proof of his Theorem 4.4.6 (p. 45) covers $G$ by finitely many sets $K \gamma_i A_\emptyset^- \gamma_j K$ with it. The decomposition $G = K A^- K$ with $K$ maximal compact holds when the centre is anisotropic (his Lemma 1.4.5, p. 15) and for $\mathrm{GL}_n$, but not for every connected reductive group: for $\mathrm{R}_{E/F}\mathbb{G}_m$ with $E/F$ ramified quadratic, $K = \mathcal{O}_E^\times$ and $A^- = F^\times$, every element of $K A^- K$ has even $E$-valuation

## Sources

- W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, notes, draft of 1 May 1995, <https://personal.math.ubc.ca/~cass/research/pdf/p-adic-book.pdf>:
  §4 (Lemma 4.1.1, Theorem 4.1.2, Jacquet's second lemma; Theorem 4.2.4, the canonical pairing;
  Theorem 4.3.3, asymptotics; §4.4 and Theorem 4.4.6, the square-integrability criterion),
  Theorems 5.2.1 and 5.3.1.
- W. Casselman, "The unramified principal series of p-adic groups I. The spherical function",
  Compositio Math. 40 (1980), 387–406, <http://www.numdam.org/item?id=CM_1980__40_3_387_0>: the
  proof of Proposition 2.4 (the use of Lemma 4.1.3 of an earlier version of the notes above).
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): (2.3.1)–(2.3.4) (essentially $L^r$ and tempered representations,
  after A. J. Silberger) and (2.3.9) (the Langlands classification for general reductive groups,
  after Silberger and Borel–Wallach).
- A. V. Zelevinsky, "Induced representations of reductive p-adic groups. II. On irreducible
  representations of GL(n)", Ann. Sci. École Norm. Sup. (4) 13 (1980), 165–210,
  <http://www.numdam.org/item?id=ASENS_1980_4_13_2_165_0>: §9.3 (the use of Casselman's criterion).
