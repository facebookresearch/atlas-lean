# Mirabolic restriction and Bernstein–Zelevinsky derivatives

This node is still to be broken down. It covers the analysis of smooth representations of
$G_n = \mathrm{GL}_n(F)$, over a non-archimedean local field $F$, through their restriction to the
mirabolic subgroup $P_n$ of matrices with last row $(0, \dots, 0, 1)$, which the proofs of
[Zelevinsky's classification](zelevinsky-classification.md), of the uniqueness of
[Whittaker models](whittaker-models-for-gl-n.md) and of Bernstein's irreducibility theorem for
[unitary representations](tempered-and-unitary-representations-of-gl-n.md) use.

- The functors $I_{U,\theta}$, $i_{U,\theta}$ and $r_{U,\theta}$ attached to closed subgroups $M$ and
  $U$ of an $\ell$-group such that $M$ normalizes $U$, $M \cap U = \{e\}$ and $MU$ is closed, and to
  a character $\theta$ of $U$ normalized by $M$: the exactness of $I_{U,\theta}$ and $i_{U,\theta}$,
  the exactness of $r_{U,\theta}$ when $U$ is a limit of compact subgroups (every compact subset of
  $U$ lies in a compact subgroup), and Frobenius reciprocity, $r_{U,\theta}$ being left adjoint to
  $I_{U,\theta}$.
- The functors $\Psi^\pm$ and $\Phi^\pm$ between representations of $P_n$, of $G_{n-1}$ and of
  $P_{n-1}$, their exactness and adjunctions, and the resulting filtration of a representation of
  $P_n$.
- The derivatives $\pi^{(k)}$ of a representation $\pi$ of $G_n$ or $P_n$, the level (the largest
  $k$ with $\pi^{(k)} \ne 0$) and the highest derivative; the theorem of Gelfand and Kazhdan on the
  derivatives of quasicuspidal representations; the Leibniz rule for the derivatives of a product;
  the derivatives of the representations $\langle \Delta \rangle$; the irreducibility of the
  highest derivative of an irreducible representation; Kirillov models.
- The Gelfand–Kazhdan method of invariant distributions, behind the uniqueness of Whittaker models
  and the description of contragredients by $g \mapsto {}^t g^{-1}$, and Bernstein's
  $P$-invariant distributions.

## Expansion

A good expansion has definition pages for the functors and for derivatives, and statement pages
for the exactness and adjunctions, the Gelfand–Kazhdan theorem on derivatives, the Leibniz rule,
the derivatives of $\langle \Delta \rangle$, the irreducibility of highest derivatives and the
Gelfand–Kazhdan theorem on invariant distributions, each citing the sources below with locators.

A good expansion also writes out these steps of its own proof:

- the application of Bernstein and Zelevinsky's Theorem 5.2 in the mirabolic situations of their Proposition 4.13 (proved in their §7), which gives the filtration of the derivatives of a product by products of derivatives (their Lemma 4.5, proved in 4.14 (c)), and Corollary 4.6 in the Grothendieck group, for the Leibniz rule.
- Bernstein's $P$-invariant distributions, by the method of invariant distributions.

## Depends on

- [Smooth and admissible representations of p-adic groups](../representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md)
- [Parabolic induction and Jacquet functors](../representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md)
- [Cuspidal representations and Jacquet's embedding theorem](../representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for quasicuspidal representations

## Proof depends on

- [The Bernstein–Zelevinsky filtration of a restriction of an induced representation](../representations-of-p-adic-reductive-groups/bernstein-zelevinsky-filtration-theorem.md), for Bernstein and Zelevinsky's Theorem 5.2 (1977), the filtration of a composition of an induction functor and a restriction functor with characters, of which the parabolic geometric lemma is the case of trivial characters (their §6.4), for the Leibniz rule
- [ℓ-spaces, distributions and smooth representations of ℓ-groups](../representations-of-p-adic-reductive-groups/l-spaces-distributions-and-smooth-representations-of-l-groups.md), for distributions on $\ell$-spaces and $\ell$-sheaves (Bernstein–Zelevinsky 1976, Chapter I, §1) and the theorems on invariant distributions (ibid., Chapter III, §6), for the Gelfand–Kazhdan method

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §1.8 and Proposition 1.9 (the functors
  $I_{U,\theta}$, $i_{U,\theta}$, $r_{U,\theta}$), §3.2 with Proposition 3.2, §3.3, §3.5
  (derivatives), Theorem 4.4 (Gelfand–Kazhdan), Lemma 4.5 and Corollary 4.6 (derivatives of
  products), Theorem 4.9 and Remark 4.10.
- I. N. Bernstein and A. V. Zelevinsky, "Representations of the group GL(n, F), where F is a local
  non-Archimedean field", Uspekhi Mat. Nauk 31 (1976), no. 3, 5–70, as cited in the papers above
  and below (chap. II; §7.3 for the theorem of Gelfand and Kazhdan on contragredients).
- A. V. Zelevinsky, "Induced representations of reductive p-adic groups. II. On irreducible
  representations of GL(n)", Ann. Sci. École Norm. Sup. (4) 13 (1980), 165–210,
  <http://www.numdam.org/item?id=ASENS_1980_4_13_2_165_0>: Theorem 3.5 and §§3.7–3.8 (derivatives
  of $\langle \Delta \rangle$), §4.3 (level), Theorem 8.1 and Corollary 8.2 (highest derivatives
  and degenerate Kirillov models).
- I. N. Bernstein, "P-invariant distributions on GL(N) and the classification of unitary
  representations of GL(N) (non-Archimedean case)", in *Lie Group Representations II*, Lecture
  Notes in Math. 1041, Springer, 1984, 50–102, as cited by Tadić (1986), Theorem 2.5.
