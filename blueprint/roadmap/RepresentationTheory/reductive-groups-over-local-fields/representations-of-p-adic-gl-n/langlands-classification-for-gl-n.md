# Langlands classification for GLₙ

Let $F$ be a non-archimedean local field, $G_n = \mathrm{GL}_n(F)$, $\nu = \lvert \det \rvert_F$,
and use the product $\times$, the segments, the relation "precedes" and the representations
$\langle \Delta \rangle^t$ of [Zelevinsky's classification](zelevinsky-classification.md).

**Theorem.**

1. Let $\Delta_1, \dots, \Delta_r$ be segments such that $\Delta_i$ does not precede $\Delta_j$
   whenever $i < j$. Then $\langle \Delta_1 \rangle^t \times \dots \times \langle \Delta_r \rangle^t$
   has a unique irreducible quotient $L(\Delta_1, \dots, \Delta_r)$, which depends only on the
   multiset $a = \{\Delta_1, \dots, \Delta_r\}$ and is denoted $L(a)$.
2. The map $a \mapsto L(a)$ is a bijection from the finite multisets of segments onto the
   isomorphism classes of irreducible smooth representations of all the $G_n$, $n \ge 0$.
3. Equivalently, in terms of
   [essentially square-integrable representations](essentially-square-integrable-representations-of-gl-n.md):
   each such $\delta$ is $\nu^{e(\delta)}\delta^u$ for a unique real number $e(\delta)$ and a unique
   square-integrable $\delta^u$; if $\delta_1, \dots, \delta_r$ are irreducible essentially
   square-integrable representations ordered so that $e(\delta_1) \ge \dots \ge e(\delta_r)$, then
   $\delta_1 \times \dots \times \delta_r$ has a unique irreducible quotient $L(\delta_1, \dots, \delta_r)$,
   and this gives a bijection from the finite multisets of irreducible essentially
   square-integrable representations onto the irreducible representations of all the $G_n$.
4. **Contragredients and sums.** For a segment $\Delta$ let $\tilde\Delta$ be the segment of the
   contragredients of its members, and for $a = \{\Delta_1, \dots, \Delta_r\}$ let
   $\tilde a = \{\tilde\Delta_1, \dots, \tilde\Delta_r\}$. Then the contragredient of $L(a)$ is
   $L(\tilde a)$. For finite multisets $a$ and $b$ of segments, $L(a + b)$ is a composition factor of
   $L(a) \times L(b)$, of multiplicity one.

It is the case of $\mathrm{GL}_n$ of Langlands's classification by tempered representations and
exponents.

## Depends on

- [Zelevinsky's classification of the irreducible representations of GLₙ](zelevinsky-classification.md), for the product, segments, the relation "precedes" and the representations $\langle \Delta \rangle^t$
- [Essentially square-integrable representations of GLₙ](essentially-square-integrable-representations-of-gl-n.md), for item 3

## Proof depends on

- [Zelevinsky's classification of the irreducible representations of GLₙ](zelevinsky-classification.md), for the irreducibility criterion for products of the $\langle \Delta_i \rangle^t$ and the rearrangement argument of its proof
- [Essentially square-integrable representations of GLₙ](essentially-square-integrable-representations-of-gl-n.md), for the bijection $\Delta \mapsto \langle \Delta \rangle^t$ onto the essentially square-integrable representations
- [Jacquet modules and the asymptotics of matrix coefficients](../representations-of-p-adic-reductive-groups/asymptotics-of-matrix-coefficients.md), for Langlands's quotient theorem for p-adic groups
- [Smooth and admissible representations of p-adic groups](../representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for contragredients, and for the distribution characters $f \mapsto \operatorname{trace} \pi(f)$ of admissible representations and their determination of composition factors, through which Tadić obtains the composition factor of item 4 as a limit of characters of irreducible representations (proof of Proposition A.4, pp. 373–374)

## Sources

- M. Tadić, "Classification of unitary representations in irreducible representations of general
  linear group (non-Archimedean case)", Ann. Sci. École Norm. Sup. (4) 19 (1986), 335–382,
  <http://www.numdam.org/item?id=ASENS_1986_4_19_3_335_0>: §5.1 ($L(\Delta)$, the unique irreducible
  quotient of $\rho \times \nu\rho \times \dots \times \nu^{m-1}\rho$), §5.2 (the representation
  $\lambda(a)$, independent of the admissible ordering "in the same way like Proposition 6.4 of
  [Zelevinsky], using Theorem 9.7, (a)", its unique irreducible quotient $L(a)$ and the bijection,
  "a version of Langlands classification", presented by F. Rodier), §§5.3–5.4 (the form with
  essentially square-integrable representations and the exponents $e(\delta)$), §1.15 (the
  segments $\tilde\Delta$ and multisets $\tilde a$), Proposition 5.6 (iii) ($L(a)^\sim = L(\tilde a)$),
  and Appendix, Proposition A.4 (i) ("$L(a + b)$ is a composition factor of $L(a) \times L(b)$"),
  proved on pp. 373–374 through the distribution characters $\mathrm{ch}_\pi(f)$, with Remark A.5
  (multiplicity one).
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): Theorem (2.2.9) (2)–(3) (with $Q(\Delta) = \langle \Delta \rangle^t$),
  (2.2.10) (existence of the ordering), (2.2.12) ($Q(\Delta_1, \dots, \Delta_r)^\vee =
  Q(\Delta_1^\vee, \dots, \Delta_r^\vee)$, after Zelevinsky 3.3 and 9.4 and Tadić 1.15 and 5.6) and
  (2.3.9) (relation with the general Langlands classification).
- A. V. Zelevinsky, "Induced representations of reductive p-adic groups. II. On irreducible
  representations of GL(n)", Ann. Sci. École Norm. Sup. (4) 13 (1980), 165–210,
  <http://www.numdam.org/item?id=ASENS_1980_4_13_2_165_0>: §9.1 ($\langle \Delta \rangle^t$ is the
  unique irreducible quotient of $\rho \times \nu\rho \times \dots \times \rho'$).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states forms of this classification over fields of characteristic zero as
  `GlobalTheory.Published.LanglandsExhaustionGL`, `GlobalTheory.Published.LanglandsMultisegments`
  and `GlobalTheory.Published.StandardCosocleGL`.
