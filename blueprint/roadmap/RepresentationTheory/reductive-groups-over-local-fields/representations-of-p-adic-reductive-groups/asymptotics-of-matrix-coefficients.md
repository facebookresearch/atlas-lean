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

## Expansion

A good expansion has statement pages for Jacquet's lemmas, the canonical pairing, the asymptotic
expansion, Casselman's square-integrability and temperedness criteria and the Langlands
classification, each citing the sources below with locators.

A good expansion also writes out these steps of its own proof:

- Each $W$-orbit meets the closed chamber of $A_\emptyset^-$, whose points in $M(F)/M(F)^1$ lie in finitely many translates of its points in $X_*(A_\emptyset)$; so $G = \bigcup_{t \in T} \tilde K\, t A_\emptyset^- \tilde K$ for a finite subset $T$ of $M(F)$, and the asymptotics are studied on each $t A_\emptyset^-$, which leaves Casselman's square-integrability criterion unaffected. For unramified groups, $\mathrm{GL}_n$ among them, $M(F)/M(F)^1 = X_*(A_\emptyset)$ and $G = \tilde K A_\emptyset^- \tilde K$. Casselman's Lemma 1.4.5 and Proposition 1.4.6 (p. 15), used in the proof of his Theorem 4.4.6 (p. 45), take the middle factor in $A_\emptyset^-$ itself, which fails in general: for $G = \mathrm{R}_{E/\mathbb{Q}_3}\mathrm{SL}_2$ with $E = \mathbb{Q}_3(\sqrt 3)$, whose centre is finite, no open subgroup $\Gamma$, compact modulo the centre and containing $A_\emptyset(\mathcal{O})$, satisfies $G = \Gamma A_\emptyset^- \Gamma$: in a basis of a $\Gamma$-stable $\mathcal{O}_E$-lattice, $\mathrm{diag}(\pi_E, \pi_E^{-1})$ is not in $\Gamma A_\emptyset^- \Gamma$, because the elements $\mathrm{diag}(t, t^{-1})$, $t \in \mathbb{Q}_3^\times$, of $A_\emptyset(F)$ have even $E$-valuations.

## Depends on

- [Smooth and admissible representations of p-adic groups](smooth-representations-of-p-adic-groups.md)
- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md)
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for Iwahori factorizations and the cones $A^-_\Theta$

## Proof depends on

- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the compact open subgroups with an Iwahori factorization in Jacquet's lemmas and for the cones $A^-_\Theta$
- [Cartan decomposition and Satake isomorphism for special maximal compact subgroups](cartan-decomposition-and-satake-isomorphism.md), for a Cartan decomposition for every connected reductive group in terms of the minimal Levi subgroup $M = Z_G(A_\emptyset)$: for the special maximal compact subgroup $\tilde K$ fixing a special vertex in the apartment of $A_\emptyset$ (this compatibility is needed; an independently chosen $\tilde K$ may fail), $\tilde K \backslash G / \tilde K \cong W \backslash M(F)/M(F)^1$ (Haines–Rostami, Introduction, pp. 1–2, after Cartier)

## Sources

- W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, notes, draft of 1 May 1995, <https://personal.math.ubc.ca/~cass/research/pdf/p-adic-book.pdf>:
  §4 (Lemma 4.1.1, Theorem 4.1.2, Jacquet's second lemma; Theorem 4.2.4, the canonical pairing;
  Theorem 4.3.3, asymptotics; §4.4 and Theorem 4.4.6, the square-integrability criterion),
  Theorems 5.2.1 and 5.3.1.
- W. Casselman, "The unramified principal series of p-adic groups I. The spherical function",
  Compositio Math. 40 (1980), 387–406, <http://www.numdam.org/item?id=CM_1980__40_3_387_0>: the
  proof of Proposition 2.4 (the use of Lemma 4.1.3 of an earlier version of the notes above).
- T. J. Haines and S. Rostami, "The Satake isomorphism for special maximal parahoric Hecke algebras",
  arXiv:0907.4506 (version 2): Introduction, pp. 1–2 (for a connected reductive group over a
  non-archimedean local field, a special maximal compact subgroup $\tilde K$ and $M = \mathrm{Cent}_G(A)$, the Cartan
  decomposition $\tilde K \backslash G(F) / \tilde K \cong W(G, A) \backslash \tilde\Lambda_M$ of Cartier, where
  $\tilde\Lambda_M = M(F)/M(F)^1$ is free abelian, contains $X_*(A)$ and has the same rank; for unramified groups it
  is $W(G, A) \backslash X_*(A)$).
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): (2.3.1)–(2.3.4) (essentially $L^r$ and tempered representations,
  after A. J. Silberger) and (2.3.9) (the Langlands classification for general reductive groups,
  after Silberger and Borel–Wallach).
- A. V. Zelevinsky, "Induced representations of reductive p-adic groups. II. On irreducible
  representations of GL(n)", Ann. Sci. École Norm. Sup. (4) 13 (1980), 165–210,
  <http://www.numdam.org/item?id=ASENS_1980_4_13_2_165_0>: §9.3 (the use of Casselman's criterion).
