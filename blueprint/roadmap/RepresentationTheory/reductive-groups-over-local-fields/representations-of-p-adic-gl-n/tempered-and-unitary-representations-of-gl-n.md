# Tempered and unitary representations of GLₙ

Let $F$ be a non-archimedean local field, $G_n = \mathrm{GL}_n(F)$ with centre $Z_n$,
$\nu = \lvert \det \rvert_F$, and use the product $\times$ and the representations
$\langle \Delta \rangle^t$ of [Zelevinsky's classification](zelevinsky-classification.md), the
[square-integrable representations](essentially-square-integrable-representations-of-gl-n.md) and
the [Langlands classification](langlands-classification-for-gl-n.md). An admissible representation
of $G_n$ is **tempered** if it has a unitary central character and its matrix coefficients are in
$L^{2+\varepsilon}(Z_n \backslash G_n)$ for every $\varepsilon > 0$.

1. **Bernstein's theorem.** If $\pi_1$ and $\pi_2$ are irreducible unitarizable representations
   of $G_{n_1}$ and $G_{n_2}$, then $\pi_1 \times \pi_2$ is irreducible and unitarizable.
2. **Tempered representations.** Let $F$ be a finite extension of $\mathbb{Q}_p$. An irreducible
   representation $L(\Delta_1, \dots, \Delta_r)$ of $G_n$ is tempered if and only if every
   $\langle \Delta_i \rangle^t$ is square-integrable; then no two of the $\Delta_i$ are linked and
   $L(\Delta_1, \dots, \Delta_r) \cong \langle \Delta_1 \rangle^t \times \dots \times \langle \Delta_r \rangle^t$.
3. **Tadić's classification.** For a square-integrable irreducible representation $\delta$ and an
   integer $m \ge 1$, the representation
   $\nu^{(m-1)/2}\delta \times \nu^{(m-3)/2}\delta \times \dots \times \nu^{-(m-1)/2}\delta$ has a
   unique irreducible quotient $u(\delta, m)$. Let $B$ be the set of the representations
   $u(\delta, m)$ and $\nu^{\alpha} u(\delta, m) \times \nu^{-\alpha} u(\delta, m)$ with $\delta$
   square-integrable, $m \ge 1$ and $0 < \alpha < 1/2$. Then every product of elements of $B$ is
   irreducible and unitarizable, and every irreducible unitarizable representation of a group $G_n$
   is such a product, with factors unique up to permutation.

Tadić's proof of item 3 in his §§7–8 uses the fact, announced by Bernstein and proved later, that
Zelevinsky's involution carries irreducible representations to irreducible ones; his Appendix
proves the main results without it when $F$ has characteristic zero.

## Depends on

- [Smooth and admissible representations of p-adic groups](../representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for unitarizable representations, matrix coefficients and central characters
- [Zelevinsky's classification of the irreducible representations of GLₙ](zelevinsky-classification.md), for the product, linked segments and the representations $\langle \Delta \rangle^t$
- [Essentially square-integrable representations of GLₙ](essentially-square-integrable-representations-of-gl-n.md), for square-integrable representations
- [Langlands classification for GLₙ](langlands-classification-for-gl-n.md), for the representations $L(\Delta_1, \dots, \Delta_r)$

## Proof depends on

- [Mirabolic restriction and Bernstein–Zelevinsky derivatives](bernstein-zelevinsky-derivatives.md), for the restriction to the mirabolic subgroup used in Bernstein's proof of item 1
- [Jacquet modules and the asymptotics of matrix coefficients](../representations-of-p-adic-reductive-groups/asymptotics-of-matrix-coefficients.md), for the criterion for temperedness by exponents used in item 2
- [Zelevinsky's classification of the irreducible representations of GLₙ](zelevinsky-classification.md)
- [Langlands classification for GLₙ](langlands-classification-for-gl-n.md)
- [Essentially square-integrable representations of GLₙ](essentially-square-integrable-representations-of-gl-n.md)

## Sources

- M. Tadić, "Classification of unitary representations in irreducible representations of general
  linear group (non-Archimedean case)", Ann. Sci. École Norm. Sup. (4) 19 (1986), 335–382,
  <http://www.numdam.org/item?id=ASENS_1986_4_19_3_335_0>: Theorem 2.5 (i) (Bernstein's theorem,
  from I. N. Bernstein, "P-invariant distributions on GL(N) and the classification of unitary
  representations of GL(N) (non-Archimedean case)", Lecture Notes in Math. 1041 (1984), 50–102),
  the definition of $u(\delta, n)$ and Theorem D in the introduction, Theorem A, the introduction's
  discussion of the role of Zelevinsky's involution and the Appendix (Theorems A.9–A.11, for
  $\mathrm{char}\, F = 0$).
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): (2.3.1) and (2.3.3) (essentially $L^r$, square-integrable and
  tempered representations), Proposition (2.3.7) (item 2, after Kudla's survey, §2.2) and (2.3.8),
  and (2.2.11) (the proofs that Zelevinsky's involution preserves irreducibility).
