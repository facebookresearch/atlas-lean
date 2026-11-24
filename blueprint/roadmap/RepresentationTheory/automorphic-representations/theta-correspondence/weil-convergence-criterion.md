# Weil's convergence criterion for theta integrals

Let $F$ be a number field, $E/F$ a quadratic extension, $W_n$ a split skew-Hermitian space of dimension
$2n$ over $E$, and $V$ a Hermitian space of dimension $m$ and Witt index $r$ over $E$. Let $\omega$ be the
[Weil representation](weil-representation-of-unitary-dual-pairs.md) of
$\mathrm{U}(W_n)(\mathbb{A}) \times \mathrm{U}(V)(\mathbb{A})$ on $\mathcal{S}(Y_n^* \otimes_E V)(\mathbb{A})$
attached to $(\psi, \chi_V)$, and $\theta(\varphi)(g, h)$ its automorphic realization, for $m, n \ge 1$. (The degenerate cases
are defined directly: if $m = 0$, then $r = 0$, $\mathrm{U}(V)$ is trivial and $\theta(\varphi)(g) = \chi_V(\iota^{-1}(\det g))\, \varphi(0)$ with
$\iota(x) = x/x^c$; if $n = 0$, the integral is $\varphi(0)$.) Then the theta integral

$$I(\varphi)(g) = \int_{\mathrm{U}(V)(F) \backslash \mathrm{U}(V)(\mathbb{A})} \theta(\varphi)(g, h)\, dh,$$

taken for the Haar measure for which $\mathrm{U}(V)(F) \backslash \mathrm{U}(V)(\mathbb{A})$ has volume $1$,
converges absolutely for every $\varphi \in \mathcal{S}(Y_n^* \otimes_E V)(\mathbb{A})$ and every $g$ if and
only if

$$r = 0 \qquad \text{or} \qquad m - r > n.$$

This is Weil's convergent range. Weil proved that the condition suffices; the converse is stated by Gan,
Qiu and Takeda, who attribute the equivalence to Weil (Weil himself asks whether his general sufficient
criterion is also necessary). The equivalence is about all $\varphi$ at once: outside the range some
$\varphi$ give divergent integrals, though others may converge. In the range the convergence is absolute for
the sum of absolute values of the terms of the theta series, which allows termwise integration, and
$I(\varphi)$ is a smooth function of moderate growth on $\mathrm{U}(W_n)(F) \backslash \mathrm{U}(W_n)(\mathbb{A})$ (a smooth
automorphic form in the sense of Gan–Qiu–Takeda, without finiteness under a maximal compact subgroup); it is
an automorphic form when $\varphi$ corresponds to a polynomial in the Fock model at every archimedean place.
If $m > 2n$, every $V$ is in the range, since $r \le m/2$. If $r = 0$, the quotient
$\mathrm{U}(V)(F) \backslash \mathrm{U}(V)(\mathbb{A})$ is compact.

## Depends on

- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for $\omega$, its Schrödinger model and $\theta(\varphi)$
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the finite volume of $\mathrm{U}(V)(F) \backslash \mathrm{U}(V)(\mathbb{A})$
- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for automorphic forms on $\mathrm{U}(W_n)(\mathbb{A})$

## Proof depends on

- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the Siegel sets of $\mathrm{U}(V)(\mathbb{A})$, the integration estimates on them (Weil's §§9–11, with the weights of the modulus character of the stabilizer of a maximal isotropic subspace, $\lvert \det \rvert_E^{m - r}$ on its $\mathrm{GL}$ factor) and their bounded overlap: for sufficiency, Weil's estimate (his §12, Lemma 5), which bounds the compact family of translated test functions pointwise by one positive Schwartz function on the vector space and sums its lattice translates on a Siegel set, specialized to unitary groups (his §51, Proposition 8); for necessity, take $g = 1$ and a non-negative test function, bounded below near $0$ at the archimedean places and a lattice indicator at the finite places, scale a rational maximal isotropic subspace by $t$ at the archimedean places in a cusp of the Siegel set, holding the other coordinates in bounded windows: the rational points in the dilated box contribute at least a constant times $t^{2[F:\mathbb{Q}]rn}$, against the modulus factor $t^{-2[F:\mathbb{Q}]r(m-r)}$ and the measure $dt/t$, so that the integral diverges when $m - r \le n$ and $r > 0$
- [Global Weil representation and theta functions](global-weil-representation-and-theta-functions.md), for the theta distribution, its transformation law and the moderate growth of $\theta(\varphi)$ in $g$

## Sources

- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3):
  §2.9, (2.2) (the one-dimensional model for $m = 0$), §2.10 (smooth automorphic forms), §3.1 ("By Weil [We1], it is known that the above integral converges if and only if $r = 0$ or
  $m - r = m_0 + r > d(n)$", with $d(n) = n$ for unitary groups, and the normalization of the measure),
  §3.6 (when $m > 2 d(n)$ one is automatically in the convergent range), and §2.3 (the split space $W_n$
  of dimension $2n$).
- S. Yamana, "On the Siegel–Weil formula: the case of singular forms", Compositio Math. 147 (2011),
  1003–1021, <https://doi.org/10.1112/S0010437X11005379>: §1.3, the convergence of the theta integral for
  all $\Phi$ when $\phi$ is anisotropic or $m - r > \varrho$ ($\varrho = n$ in the unitary case 2).
- A. Weil, "Sur la formule de Siegel dans la théorie des groupes classiques", Acta Math. 113 (1965),
  1–87, <https://doi.org/10.1007/BF02391774>: §§9–11 (reduction theory and an integration estimate), §12,
  Lemma 5 and the remark after it (the estimate of the theta series, and the question whether the
  condition is necessary), Chapter II, §27 (type I₂), and Chapter VI, §51, Proposition 8 (the unitary case:
  convergence whenever $m - r > n$), the source GQT cite.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the sufficiency, for $n \ge 1$ and all Schwartz data, as
  `GlobalTheory.Published.WeilThetaConvergence`.
