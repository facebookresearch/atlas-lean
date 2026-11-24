# Whittaker models and the Gelfand–Kazhdan theorems for GLₙ

Let $F$ be a non-archimedean local field, $G_n = \mathrm{GL}_n(F)$, $U_n$ its subgroup of upper
triangular unipotent matrices, and $\psi$ a nontrivial additive character of $F$. For a
character $\theta$ of $U_n$, let $I(\theta)$ be the smooth representation of $G_n$ induced from
$\theta$: right translation on the functions $f \colon G_n \to \mathbb{C}$ with
$f(ug) = \theta(u)f(g)$ that are right invariant under some open subgroup. Let
$\theta_\psi(u) = \psi(u_{12} + u_{23} + \dots + u_{n-1,n})$. An irreducible smooth representation
$\pi$ of $G_n$ is **generic** if $\mathrm{Hom}_{U_n}(\pi, \theta_\psi) \ne 0$; this does not depend
on $\psi$.

1. **Uniqueness of Whittaker models** (Gelfand–Kazhdan). For every irreducible smooth
   representation $\pi$ of $G_n$, $\dim \mathrm{Hom}_{U_n}(\pi, \theta_\psi) \le 1$. If $\pi$ is
   generic and $0 \ne \lambda \in \mathrm{Hom}_{U_n}(\pi, \theta_\psi)$, then
   $v \mapsto (g \mapsto \lambda(\pi(g)v))$ embeds $\pi$ into $I(\theta_\psi)$; its image is the
   Whittaker model $\mathcal{W}(\pi, \psi)$.
2. **Degenerate Whittaker models** (Zelevinsky). Let $\omega$ be an irreducible representation of
   $G_n$. Put $\omega_0 = \omega$ and, inductively, let $\lambda_i$ be the level of
   $\omega_{i-1}$ (the largest $k$ with $\omega_{i-1}^{(k)} \ne 0$) and
   $\omega_i = \omega_{i-1}^{(\lambda_i)}$ its highest derivative; let $k$ be the least index with
   $\lambda_1 + \dots + \lambda_k = n$. Let $\theta(u) = \psi(\sum_i u_{i,i+1})$, the sum over
   $1 \le i \le n-1$ with $i$ different from $n - \lambda_1, n - \lambda_1 - \lambda_2, \dots,
   n - \lambda_1 - \dots - \lambda_{k-1}$. Then $\dim \mathrm{Hom}_{G_n}(\omega, I(\theta)) = 1$, so
   $\omega$ embeds into $I(\theta)$ in a unique way up to a scalar. For generic $\omega$,
   $\theta = \theta_\psi$.
3. **Generic representations.** An irreducible representation is generic if and only if it is
   isomorphic to $\langle \Delta_1 \rangle^t \times \dots \times \langle \Delta_r \rangle^t$ for
   segments $\Delta_1, \dots, \Delta_r$ no two of which are linked; the multiset
   $\{\Delta_1, \dots, \Delta_r\}$ is then determined by the representation.
4. **Contragredients** (Gelfand–Kazhdan). For every irreducible smooth representation $\pi$ of
   $G_n$, the contragredient $\tilde\pi$ is isomorphic to the representation
   $g \mapsto \pi({}^t g^{-1})$.

## Depends on

- [Smooth and admissible representations of p-adic groups](../representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md)
- [Mirabolic restriction and Bernstein–Zelevinsky derivatives](bernstein-zelevinsky-derivatives.md), for derivatives and levels, used in item 2
- [Zelevinsky's classification of the irreducible representations of GLₙ](zelevinsky-classification.md), for the product, linked segments and the representations $\langle \Delta \rangle^t$, used in item 3

## Proof depends on

- [Mirabolic restriction and Bernstein–Zelevinsky derivatives](bernstein-zelevinsky-derivatives.md), for the irreducibility of highest derivatives, the Frobenius reciprocity for the functors $I_{U,\theta}$ and $r_{U,\theta}$, and the Gelfand–Kazhdan method of invariant distributions
- [Zelevinsky's classification of the irreducible representations of GLₙ](zelevinsky-classification.md)

## Sources

- A. V. Zelevinsky, "Induced representations of reductive p-adic groups. II. On irreducible
  representations of GL(n)", Ann. Sci. École Norm. Sup. (4) 13 (1980), 165–210,
  <http://www.numdam.org/item?id=ASENS_1980_4_13_2_165_0>: §4.3 (level), Theorem 8.1 (the highest
  derivative of an irreducible representation is irreducible), §8.3 and its Corollary ("$\omega$
  may be in a unique way realized as a submodule of $I(\theta)$", a degenerate Whittaker model,
  "cf. [8], p. 97, Thm. 2", I. M. Gelfand and D. A. Kazhdan, in *Lie Groups and Their
  Representations*, Budapest, 1974), Theorem 9.7 (item 3, where generic representations are called
  non-degenerate).
- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §1.8 (the functor $I_{U,\theta}$),
  Proposition 1.9 (b), Theorem 4.9 and Remark 4.10 (the Gelfand–Kazhdan conjecture).
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): (2.4.2) (generic representations), Proposition (2.4.3)
  (independence of $\psi$), Theorem (2.4.4) (item 3), (2.4.6) (Whittaker models) and (2.1.22) (3)
  (item 4, "a theorem of Gelfand and Kazhdan ([BZ1] 7.3)", that is Bernstein–Zelevinsky, Uspekhi
  Mat. Nauk 31 (1976), §7.3).
