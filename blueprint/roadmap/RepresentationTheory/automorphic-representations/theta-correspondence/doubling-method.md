# Doubling method and standard L-functions of unitary groups

This node is still to be broken down. It covers the doubling method of Piatetski-Shapiro and Rallis for
unitary groups and the standard $L$-functions it defines. Let $F$ be a number field, $E/F$ a quadratic
extension, $U$ a skew-Hermitian space of dimension $n$ over $E$, $W_n = U \oplus U^-$ the doubled space,
$\iota \colon \mathrm{U}(U) \times \mathrm{U}(U) \to \mathrm{U}(W_n)$ the natural map, $\chi$ a Hecke character
of $\mathbb{A}_E^\times / E^\times$ with $\chi(\bar x) = \chi(x)^{-1}$, and $\pi$ a cuspidal automorphic
representation of $\mathrm{U}(U)(\mathbb{A})$.

- **Global zeta integral.** For a holomorphic section $\Phi$ of $I_n(s, \chi)$ and $f_1, f_2 \in \pi$,
  $Z(s, \Phi, f_1, f_2) = \int_{[\mathrm{U}(U)] \times [\mathrm{U}(U)]} E(s, \Phi)(\iota(g_1, g_2))\, \overline{f_1(g_1)}\, f_2(g_2)\, \chi^{-1}(\det g_2)\, dg_1\, dg_2$,
  with the [Siegel Eisenstein series](siegel-eisenstein-series-on-unitary-groups.md) $E(s, \Phi)$,
  converges for $\operatorname{Re} s \gg 0$ and extends to a meromorphic function of $s$.
- **Basic identity and Euler product.** For $\operatorname{Re} s \gg 0$ the global integral unfolds to
  an integral over $\mathrm{U}(U)(\mathbb{A})$ of $\Phi_s(\iota(g, 1))$ against a matrix coefficient of
  $\pi$, and for factorizable data it is the Euler product of the local zeta integrals
  $Z_v(s, \Phi_v, f_{1,v}, f_{2,v}) = \int_{\mathrm{U}(U)(F_v)} \Phi_v(\iota(g_v, 1))\, \overline{\langle \pi_v(g_v) f_{1,v}, f_{2,v} \rangle}\, dg_v$.
- **Local theory.** The local zeta integrals converge for $\operatorname{Re} s \gg 0$ and continue
  meromorphically; at a finite place they are rational in $q_v^{-s}$ for good sections and span a
  fractional ideal of $\mathbb{C}[q_v^{s}, q_v^{-s}]$; the standard local factors
  $L(s, \pi_v \times \chi_v)$ and $\varepsilon(s, \pi_v \times \chi_v, \psi_v)$ of Lapid and Rallis, and
  Yamana's theorem that $L(s + \tfrac12, \pi_v \times \chi_v)$ is the gcd of the zeta integrals of good
  sections; the normalized integrals $Z_v^* = Z_v / L(s + \tfrac12, \pi_v \times \chi_v)$, entire and
  non-vanishing at a given point for suitable data.
- **Unramified computation.** For unramified data, $Z_v = L(s + \tfrac12, \pi_v \times \chi_v) / d_v(s, \chi_v)$
  with $d_v$ an explicit product of Hecke $L$-factors, $L(s, \pi_v \times \chi_v)$ being the $L$-factor of
  the base change of $\pi_v$ twisted by $\chi_v$; this includes the places that split in $E$, where
  $\mathrm{U}(U)(F_v) \cong \mathrm{GL}_n(F_v)$.
- **Global consequences.** The standard $L$-function $L(s, \pi \times \chi) = \prod_v L(s, \pi_v \times \chi_v)$,
  the absolute convergence of $Z^* = \prod_v Z_v^*$ for $\operatorname{Re} s > 0$, the factorization
  $Z = L(s + \tfrac12, \pi \times \chi)\, Z^*$, the resulting form of the
  [Rallis inner product formula](rallis-inner-product-formula.md), and the holomorphy of
  $L(s + \tfrac12, \pi \times \chi_V)$ at $s_{m,n}$ when every local theta lift is non-zero.

A good expansion has pages for the global zeta integral and its meromorphic continuation, the basic
identity and the Euler product, the local zeta integrals with their rationality and good sections, the
local $L$- and $\varepsilon$-factors of Lapid and Rallis and Yamana's gcd theorem, the unramified computation
(inert and split places), and the global $L$-function with the factorization of $Z$, each citing the
sources below with locators; the closed sources (Piatetski-Shapiro–Rallis, Lapid–Rallis, Yamana's
Inventiones paper) should be consulted for the exact statements and hypotheses.

## Depends on

- [Siegel Eisenstein series on unitary groups](siegel-eisenstein-series-on-unitary-groups.md), for $I_n(s, \chi)$ and $E(s, \Phi)$
- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for cusp forms and cuspidal automorphic representations
- [Tensor product theorem for automorphic representations](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the local components $\pi_v$ and factorizable data
- [Meromorphic continuation of Hecke L-functions](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for the Hecke $L$-factors in $d_v(s, \chi_v)$

## Sources

- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3, TeX
  source): §1.5 (the doubling zeta integral and its local theory, after I. I. Piatetski-Shapiro and
  S. Rallis, *L-functions for the classical groups*, Lecture Notes in Math. 1254, Springer, 1987, Part A;
  E. Lapid and S. Rallis, in *Automorphic representations, L-functions and applications*, de Gruyter,
  2005, 309–359; and S. Yamana, "L-functions and theta correspondence for classical groups", cited as [Y4]),
  §11.5 (the global zeta integral, its convergence
  and meromorphic continuation), §11.6 (Euler product, local zeta integrals, $L$-factors, gcd property,
  normalized integrals, unramified computation with $d_v$ from [LR, p. 334, Remark 3], absolute
  convergence of $Z^*$ for $\operatorname{Re} s > 0$), Theorem 11.4 (the $L \cdot Z^*$ form of the Rallis
  inner product formula and the holomorphy of $L(s + \tfrac12, \pi \times \chi_V)$ at $s_{m,n}$).
- M. Harris, S. S. Kudla and W. J. Sweet, "Theta dichotomy for unitary groups", J. Amer. Math. Soc. 9
  (1996), 941–1004, <https://doi.org/10.1090/S0894-0347-96-00198-1>: introduction, (0.7)–(0.8) (the
  unramified factors are those of the base change), §6, (6.12)–(6.13) (local zeta integrals), Definition 6.4
  (good sections), Proposition 6.6 (rationality, the ideal and the functional equation), (6.20)–(6.22)
  (the local $L$- and $\varepsilon$-factors at a finite place).
- S. Yamana, "The Siegel–Weil formula for unitary groups", Pacific J. Math. 264 (2013), 235–257,
  <https://doi.org/10.2140/pjm.2013.264.235>: Appendix (zeta integrals for $\mathrm{GL}_n(D)$, the split
  places, after Piatetski-Shapiro–Rallis and Lapid–Rallis: convergence, meromorphic continuation and
  functional equation, Proposition A.3 relating the doubling $\gamma$-factor to Godement–Jacquet factors,
  the relation through which Piatetski-Shapiro and Rallis compute the unramified integrals, and Lemma A.4).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states related results as `GlobalTheory.Published.DoublingMethod` and
  `GlobalTheory.Published.DoublingMethodLocalZetaIntegrals` (meromorphic continuation, the basic identity for
  $\operatorname{Re} s > n/2$ and the continuation of the zeta integral) and
  `GlobalTheory.Published.UnramifiedDoublingGL` (the unramified computation at the split places).
