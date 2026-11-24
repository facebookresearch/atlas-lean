# Doubling method and standard L-functions of unitary groups

This node is still to be broken down. It covers the doubling method of Piatetski-Shapiro and Rallis for
unitary groups and the standard $L$-functions it defines. Let $F$ be a number field, $E/F$ a quadratic
extension, $U$ a skew-Hermitian space of dimension $n \ge 1$ over $E$, $W_n = U \oplus U^-$ the doubled space,
$\iota \colon \mathrm{U}(U) \times \mathrm{U}(U) \to \mathrm{U}(W_n)$ the natural map, $\chi$ a Hecke character of
$\mathbb{A}_E^\times / E^\times$ with $\chi(\bar x) = \chi(x)^{-1}$, and $\pi$ a cuspidal automorphic representation of
$\mathrm{U}(U)(\mathbb{A})$, with the Petersson pairing linear in its first variable. Fix the ordering of the two
places of $E$ above each split place of $F$, a non-trivial character $\psi = \otimes_v \psi_v$ of $\mathbb{A}_F/F$ (extended to $E_v$
through the trace), Tamagawa measures, and local pairings and measures whose products are the global ones.

- **Global zeta integral.** For a holomorphic section $\Phi$ of $I_n(s, \chi)$ and $f_1, f_2 \in \pi$,
  $Z(s, \Phi, f_1, f_2) = \int_{[\mathrm{U}(U)] \times [\mathrm{U}(U)]} E(s, \Phi)(\iota(g_1, g_2))\, \overline{f_1(g_1)}\, f_2(g_2)\, \chi^{-1}(\det g_2)\, dg_1\, dg_2$,
  with the [Siegel Eisenstein series](siegel-eisenstein-series-on-unitary-groups.md) $E(s, \Phi)$; it
  converges absolutely in the half-plane of absolute convergence of the series and extends to a meromorphic
  function of $s$.
- **Basic identity and Euler product.** For $\operatorname{Re} s$ large, the double cosets
  $Q(F) \backslash \mathrm{U}(W_n)(F) / \iota(\mathrm{U}(U) \times \mathrm{U}(U))(F)$ contribute only through the open orbit, the
  others vanishing by cuspidality, and the integral unfolds to
  $\int_{\mathrm{U}(U)(\mathbb{A})} \Phi_s(\iota(g, 1))\, \overline{\langle \pi(g) f_1, f_2 \rangle}\, dg$. For factorizable data this is
  the product of the local integrals
  $Z_v(s, \Phi_v, f_{1,v}, f_{2,v}) = \int_{\mathrm{U}(U)(F_v)} \Phi_v(\iota(g_v, 1))\, \overline{\langle \pi_v(g_v) f_{1,v}, f_{2,v} \rangle}\, dg_v$,
  in which the coefficient $\overline{\langle \pi_v(g_v) f_{1,v}, f_{2,v} \rangle}$ is a matrix coefficient of the contragredient $\pi_v^\vee$.
  Accordingly, at every place (finite, archimedean, ramified or not) this page writes
  $L(s, \pi_v \times \chi_v) := L_{\mathrm{LR}}(s, \pi_v^\vee \times \chi_v)$, and similarly for the normalized $\gamma$- and $\varepsilon$-factors with
  respect to $\psi_v$, where $L_{\mathrm{LR}}$, $\gamma_{\mathrm{LR}}$, $\varepsilon_{\mathrm{LR}}$ are the factors of Lapid and Rallis in the convention of the
  ordinary coefficient $\langle \pi_v(g) f_{1,v}, f_{2,v} \rangle$ (that of Yamana and of Harris–Kudla–Sweet); these are the factors used in
  $Z_v^*$, $Z^*$ and the global product below.
- **Local theory.** At a finite place, for good sections, the local integrals are rational in $q_v^{-s}$
  and span a fractional ideal of $\mathbb{C}[q_v^{s}, q_v^{-s}]$; the local factors $L(s, \pi_v \times \chi_v)$ and
  $\varepsilon(s, \pi_v \times \chi_v, \psi_v)$ (in the convention just fixed) are defined from the normalized $\gamma$-factor of the
  local functional equation, and Yamana's theorem identifies $L(s + \tfrac12, \pi_v \times \chi_v)$ with the generator of
  that ideal. At an archimedean place the factors are those of Lapid and Rallis, defined through the
  Langlands parameter, in the same convention. The normalized integrals
  $Z_v^* = Z_v / L(s + \tfrac12, \pi_v \times \chi_v)$ are entire, and for each $s_1$ with $\operatorname{Re} s_1 \ge 0$ there are a standard
  section and vectors with $Z_v^*(s_1) \ne 0$.
- **Unramified computation and orientation.** At a finite place where all data are unramified, with
  $\mathrm{vol}(K_v) = 1$, the normalized spherical section ($\Phi^\circ_v(1) = 1$) and spherical vectors with
  $\langle f_{1,v}, f_{2,v} \rangle = 1$: $Z_v = L_v / d_v(s, \chi_v)$ with
  $d_v(s, \chi) = \prod_{j=1}^n L_{F_v}(2s + j, \chi|_{F_v^\times}\, \varepsilon_{E_v/F_v}^{n+j})$, where $L_v$ is the standard
  $L$-factor at $s + \tfrac12$ of the base change of $\pi_v^\vee$ twisted by $\chi_v$, equivalently of
  $\mathrm{BC}(\pi_v) \otimes \chi_v^{-1}$ after applying the Galois conjugation $c$ of $E_v$ over $F_v$ (a field automorphism when $v$ does not
  split, the exchange of the two components when it splits). Gan, Qiu and Takeda write this
  factor $L(s + \tfrac12, \pi_v \times \chi_v)$ with the conjugated coefficient above; Harris–Kudla–Sweet and
  Yamana use the ordinary coefficient $\langle \pi_v(g) f_{1,v}, f_{2,v} \rangle$ and the factor of $\mathrm{BC}(\pi_v) \otimes \chi_v$.
  For example, at a split place with $n = 1$, $\pi_v = \alpha$ and $\chi_v = (\beta, \beta^{-1})$ unramified, the
  conjugated integral is $\sum_{k \in \mathbb{Z}} (\beta/\alpha)(\varpi)^k x^{\lvert k \rvert}$ with $x = q_v^{-(s+1/2)}$: its
  numerator is the pair of factors of $\beta/\alpha$ and $\alpha/\beta$, not of $\beta\alpha$ and $(\beta\alpha)^{-1}$.
- **Factorization.** For factorizable holomorphic data, $Z^* = \prod_v Z_v^*$ converges absolutely for
  $\operatorname{Re} s > 0$ and $Z = L(s + \tfrac12, \pi \times \chi)\, Z^*$ there, first in a right half-plane and then by
  meromorphic continuation, where $L(s, \pi \times \chi) = \prod_v L(s, \pi_v \times \chi_v)$ in the convention above.
- **Rallis inner product formula, $L$-function form** (Gan–Qiu–Takeda, Theorem 11.4). Let $V$ be a
  Hermitian space of dimension $m$ and Witt index $r$ with $n < m \le 2n$, $r \le n$, $m - r > n$, $\chi = \chi_V$,
  and suppose that the global theta lifts of $\pi$ to the smaller spaces of the Witt tower of $V$ vanish.
  Then the [Rallis inner product formula](rallis-inner-product-formula.md) and the factorization give
  $\langle \theta(\varphi_1, f_1), \theta(\varphi_2, f_2) \rangle = [E : F] \cdot \mathrm{Val}_{s = s_{m,n}}\bigl(L(s + \tfrac12, \pi \times \chi_V)\, Z^*(s, \varphi_1 \otimes \overline{\varphi_2}, f_1, f_2)\bigr)$,
  the value at $s_{m,n} = \tfrac{m-n}{2}$ of the product (not a residue). If moreover the local theta lift of
  $\pi_v$ is non-zero at every place, then $L(s + \tfrac12, \pi \times \chi_V)$ is holomorphic at $s_{m,n}$ and the
  value is $[E : F]\, L(s_{m,n} + \tfrac12, \pi \times \chi_V)\, Z^*(s_{m,n}, \dots)$; the proof of this refinement combines
  Yamana's pole theorem with the persistence of theta lifts up a Witt tower, which together give a non-zero lift of
  $\pi$ to a Hermitian space of the complementary dimension $2n - m$ with the same splitting character, and the vanishing
  of the lower lifts in the tower of $V$, which excludes that tower; it then uses, separately, the local conservation
  relation. (In
  the range considered here, the complementary space in the tower of $V$ would also need Witt index
  $n - (m - r) < 0$; for $n = 1$, $m = 2$, $r = 0$, the tower of an anisotropic plane does not contain the zero space.)

## Expansion

A good expansion has pages, in this order, for the global zeta integral and its continuation, the basic
identity (open orbit and vanishing of the other orbits) and the Euler product, the local zeta integrals
with their rationality and good sections, the local $L$- and $\varepsilon$-factors of Lapid and Rallis and Yamana's gcd
theorem, the unramified computation with its normalizations and orientation (inert and split places), the
factorization $Z = L Z^*$ for factorizable sections (extended to finite sums of them by linearity), the
$L$-function form of the Rallis inner product formula with all its hypotheses, and the inputs of its
refinement: Yamana's pole theorem for $L(s + \tfrac12, \pi \times \chi_V)$, which together with persistence up the tower
gives a non-zero lift to a space of the complementary dimension $2n - m$ with the same splitting character, the
vanishing of the lower lifts, which excludes the tower of $V$, and the local conservation relation, each citing the sources below with locators; the closed sources (Piatetski-Shapiro–Rallis,
Lapid–Rallis, Yamana's Inventiones paper) should be consulted for the exact statements.

A good expansion also writes out these steps of its own proof:

- the orbits of $Q(F)$ on $\mathrm{U}(W_n)(F) / \iota(\mathrm{U}(U) \times \mathrm{U}(U))(F)$ and the vanishing, by cuspidality, of the contributions of all but the open orbit (Piatetski-Shapiro and Rallis), for the basic identity.
- the step of Gan–Qiu–Takeda's proof of Theorem 11.4 (ii) (TeX lines 4237–4245) that places the space $V^\#$ given by the pole in another Witt tower: the hypothesis that the lower lifts in the tower of $V$ vanish excludes that tower, for the refinement.
- the place $v$ where $V$ and $V^\#$ lie in different local Witt towers (a non-split place; at a split place they cannot differ), at which the two localized spaces have dimensions summing to $m + (2n - m) = 2n$, below the bound $2n + 2$ of the conservation relation (Gan–Qiu–Takeda, TeX lines 4245–4252); nothing is claimed about all the Witt towers at a place, for the refinement.

## Depends on

- [Siegel Eisenstein series on unitary groups](siegel-eisenstein-series-on-unitary-groups.md), for $I_n(s, \chi)$ and $E(s, \Phi)$
- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for cusp forms and cuspidal automorphic representations
- [Tensor product theorem for automorphic representations](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the local components $\pi_v$ and factorizable data
- [Meromorphic continuation of Hecke L-functions](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for the Hecke $L$-factors in $d_v(s, \chi_v)$
- [Rallis inner product formula in Weil's convergent range](rallis-inner-product-formula.md), for the integral form of the Rallis inner product formula, from which the $L$-function form follows
- [Global theta lifts of cusp forms](global-theta-lifts.md), for the theta lifts and the tower hypothesis in the $L$-function form

## Proof depends on

- [Constant terms of theta lifts for unitary groups](constant-terms-of-theta-lifts.md), for the persistence of a nonzero theta lift up a Witt tower, in the refinement: if the lift $\theta_{n,r}(\varphi, f)$ is nonzero, extending $\varphi$ by a Schwartz factor equal to $1$ at zero gives a datum for $V_{r+1}$ whose lift has $\theta_{n,r}(\varphi, f)$ in its constant term (its constant term formula), so the higher lift is nonzero too (Wu, §3, Proposition 3.1); cuspidality at the first occurrence alone would allow a zero lift
- [Poles of L-functions and nonvanishing of global theta lifts](poles-of-doubling-l-functions-and-nonvanishing-of-theta-lifts.md), for Yamana's Theorem 10.1 (2) [Y4], as Gan, Qiu and Takeda use it with the tower property, by which, for $n < m \le 2n$ and $r \le n$ with the lower lifts vanishing, a pole of $L(s + \tfrac12, \pi \times \chi_V)$ at $s_{m,n}$ gives a nonzero theta lift of $\pi$ to a Hermitian space $V^\#$ of dimension $2n - m$ with the same splitting character, for the refinement
- [Conservation relations for the local theta correspondence](conservation-relations-for-local-theta-correspondence.md), for the lower bound for unitary dual pairs: if $\pi_v$ has nonzero theta lifts, for the same additive and splitting characters, to Hermitian spaces in different Witt towers, their dimensions, which are at least the first occurrence indices of the two towers, sum to at least $2n + 2$ (Sun–Zhu, Theorem 1.10 at a non-archimedean place, and the inequality (85) of Theorem 7.6 at an archimedean one)
- [Local–global principle for Hermitian spaces over a quadratic extension](../../../NumberTheory/quadratic-forms-sums-of-squares/hermitian-local-global-principle.md), for the existence of a place where $V$ and $V^\#$ lie in different local Witt towers: if they lay in the same tower at every place, adding hyperbolic planes to reach equal dimensions would give spaces isometric at every place, hence isometric, and $V^\#$ would lie in the tower of $V$

## Sources

- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3, TeX
  source): §1.5 (the doubling zeta integral and its local theory, after I. I. Piatetski-Shapiro and
  S. Rallis, *L-functions for the classical groups*, Lecture Notes in Math. 1254, Springer, 1987, Part A;
  E. Lapid and S. Rallis, in *Automorphic representations, L-functions and applications*, de Gruyter,
  2005, 309–359; and S. Yamana, "L-functions and theta correspondence for classical groups", cited as [Y4]),
  §11.5 (the global zeta integral, its convergence and meromorphic continuation), §11.6 (Euler product,
  local zeta integrals, $L$-factors, gcd property, normalized integrals and the existence of data with
  $Z_v^*(s_1) \ne 0$ for $\operatorname{Re} s_1 \ge 0$, unramified computation with $d_v$ from [LR, p. 334, Remark 3],
  absolute convergence of $Z^*$ for $\operatorname{Re} s > 0$), Theorem 1.3 and Theorem 11.4 with its proof (the
  $L \cdot Z^*$ form of the Rallis inner product formula, its hypotheses, and the holomorphy of
  $L(s + \tfrac12, \pi \times \chi_V)$ at $s_{m,n}$ under local non-vanishing; TeX lines 4237–4252 of that proof:
  Yamana's [Y4, Theorem 10.1 (2)] with the tower property, the vanishing of the lower lifts, and the conservation
  relation, citing Kudla–Rallis, Gan–Ichino [GI2, Theorem 5.4] and Sun–Zhu).
- B. Sun and C.-B. Zhu, "Conservation relations for local theta correspondence", arXiv:1204.2969 (version 3):
  Theorem 1.10 (the conservation relations for the first occurrences in two Witt towers) and §7, Theorem 7.6,
  (84)–(85).
- S. Yamana, "The Siegel–Weil formula for unitary groups", Pacific J. Math. 264 (2013), 235–257,
  <https://doi.org/10.2140/pjm.2013.264.235>: §1, the factor $b(s, \chi) = \prod_{j=1}^{n} L(2s + j, \chi^0 \epsilon_{E/F}^{n+j})$
  (for $\delta = 1$); Appendix (zeta integrals for $\mathrm{GL}_n(D)$ at the split places, with the ordinary
  coefficient $\langle \pi(g)\xi, \xi^\vee \rangle$: convergence, meromorphic continuation and functional equation,
  Proposition A.3 relating the doubling $\gamma$-factor to the Godement–Jacquet factors of $\pi \otimes \chi_1$ and
  $\pi^\vee \otimes \chi_2$, and Lemma A.4, the unramified computation).
- M. Harris, S. S. Kudla and W. J. Sweet, "Theta dichotomy for unitary groups", J. Amer. Math. Soc. 9
  (1996), 941–1004, <https://doi.org/10.1090/S0894-0347-96-00198-1>: introduction, (0.7)–(0.8) (the
  unramified factors are those of the base change, for the ordinary coefficient), §6, (6.12)–(6.13) (local
  zeta integrals), Definition 6.4 (good sections), Proposition 6.6 (rationality, the ideal and the
  functional equation), (6.20)–(6.22) (the local $L$- and $\varepsilon$-factors at a finite place).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states related results for positive rank, flat sections and CM data as
  `GlobalTheory.Published.DoublingMethod` and `GlobalTheory.Published.DoublingMethodLocalZetaIntegrals`
  (meromorphic continuation, the basic identity for $\operatorname{Re} s > n/2$ and the continuation of the zeta
  integral), and `GlobalTheory.Published.UnramifiedDoublingGL` (an unramified computation at the split places,
  with $\mathrm{vol}(K) = 1$ and the untwisted pair of factors).
