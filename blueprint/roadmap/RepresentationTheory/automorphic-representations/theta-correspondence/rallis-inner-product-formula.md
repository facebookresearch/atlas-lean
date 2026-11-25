# Rallis inner product formula in Weil's convergent range

Let $F$ be a number field, $E/F$ a quadratic extension, $U$ a skew-Hermitian space of dimension $n$ over
$E$, and $V$ a Hermitian space of dimension $m$ and Witt index $r$ over $E$ with

$$n < m \le 2n, \qquad r \le n, \qquad m - r > n,$$

so that $V$ is in [Weil's convergent range](weil-convergence-criterion.md) for $\mathrm{U}(U \oplus U^-)$.
Fix $\psi$ and Hecke characters $(\chi_U, \chi_V)$ as for the
[Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), let
$\omega = \omega_{\psi, \chi_U, \chi_V}$ act on $\mathcal{S}(X)(\mathbb{A})$ ($m, n \ge 1$; $r = 0$ is allowed, and then the
condition on lower lifts below is empty), and let $\pi$ be a cuspidal
automorphic representation of $\mathrm{U}(U)(\mathbb{A})$ whose [global theta lifts](global-theta-lifts.md)
$\Theta_{n,j}(\pi)$ to the smaller spaces $V_j$, $j < r$, of the Witt tower of $V$ vanish, so that the functions in
$\Theta_{n,r}(\pi)$ are cuspidal in the sense that their constant terms along proper parabolic subgroups vanish. Let $W_n = U \oplus U^-$ be the
doubled space and $\iota \colon \mathrm{U}(U) \times \mathrm{U}(U) \to \mathrm{U}(W_n)$ the natural map. For
$\varphi_1, \varphi_2 \in \mathcal{S}(X)(\mathbb{A})$ such that the Schwartz function
$\delta(\varphi_1 \otimes \overline{\varphi_2})$ on $(Y_n^* \otimes_E V)(\mathbb{A})$ given by the doubling isomorphism
$\delta$ corresponds to a polynomial in the Fock model at every archimedean place (for instance, $\varphi_1$ and
$\varphi_2$ polynomial vectors in the Fock models, that is, finite under the maximal compact subgroup of the ambient
real symplectic groups; finiteness under the maximal compact subgroups of the two members of the dual pair is
not enough), let $f^{(s)}$ be its
[Siegel–Weil section](siegel-weil-formula-convergent-range.md) in $I_n(s, \chi_V)$, so that
the [Siegel Eisenstein series](siegel-eisenstein-series-on-unitary-groups.md) $E(s, f)$ is holomorphic at
$s_{m,n} = \tfrac{m - n}{2}$. Then for all cusp forms $f_1, f_2 \in \pi$

$$\bigl\langle \theta_{n,r}(\varphi_1, f_1), \theta_{n,r}(\varphi_2, f_2) \bigr\rangle = [E : F] \int_{[\mathrm{U}(U)] \times [\mathrm{U}(U)]} E(s_{m,n}, f)\bigl(\iota(g_1, g_2)\bigr)\, \overline{f_1(g_1)}\, f_2(g_2)\, \chi_V^{-1}(\det g_2)\, dg_1\, dg_2,$$

where $[\mathrm{U}(U)] = \mathrm{U}(U)(F) \backslash \mathrm{U}(U)(\mathbb{A})$, the left side is the Petersson
inner product $\int_{[\mathrm{U}(V)]} \theta_1(h) \overline{\theta_2(h)}\, dh$, all measures are Tamagawa
measures, and both sides converge absolutely. The integral on the right is the doubling zeta integral
$Z(s_{m,n}, f, f_1, f_2)$, so the right side is $[E : F]\, Z(s_{m,n}, f, f_1, f_2) = 2 Z(s_{m,n}, f, f_1, f_2)$; the
pairing is with the value of the continued series $E(s, f)$ at $s_{m,n}$, whose defining sum need not
converge there. The form of this identity through the standard $L$-function of $\pi$ is stated in the
[doubling method](doubling-method.md) node.

## Depends on

- [Global theta lifts of cusp forms](global-theta-lifts.md), for $\theta_{n,r}(\varphi, f)$ and the vanishing of the lower lifts
- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for $\omega$, the doubled space and the isomorphism $\delta$
- [Siegel–Weil formula for unitary groups in Weil's convergent range](siegel-weil-formula-convergent-range.md), for the Siegel–Weil section and the holomorphy of $E(s, f)$ at $s_{m,n}$
- [Siegel Eisenstein series on unitary groups](siegel-eisenstein-series-on-unitary-groups.md), for $I_n(s, \chi_V)$ and $E(s, f)$
- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for cusp forms and cuspidal automorphic representations

## Proof depends on

- [Siegel–Weil formula for unitary groups in Weil's convergent range](siegel-weil-formula-convergent-range.md), for the identification of the inner theta integral: with Tamagawa measure, $\int_{[\mathrm{U}(V)]} \theta(\delta(\varphi_1 \otimes \overline{\varphi_2}))(\iota(g_1, g_2), h)\, dh = \tau(\mathrm{U}(V)) \cdot E(s_{m,n}, f)(\iota(g_1, g_2)) = 2 E(s_{m,n}, f)(\iota(g_1, g_2))$, since the formula holds with constant $\kappa = 1$ (as $m > n$) for the probability measure
- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for the doubling see-saw: through $\delta$, the product $\theta(\varphi_1)(g_1, h)\overline{\theta(\varphi_2)(g_2, h)}$ equals $\theta(\delta(\varphi_1 \otimes \overline{\varphi_2}))(\iota(g_1, g_2), h)$ times $\chi_V^{-1}(\det g_2)$
- [Weil's convergence criterion for theta integrals](weil-convergence-criterion.md), for the absolute convergence of the theta integral over $[\mathrm{U}(V)]$, which with the rapid decay of the cusp forms justifies the exchange of integrals
- [Rapid decay of cusp forms](../automorphic-forms-on-reductive-groups/rapid-decay-of-cusp-forms.md), for the rapid decrease of $f_1$ and $f_2$ against the moderate growth of the theta functions
- [Global Weil representation and theta functions](global-weil-representation-and-theta-functions.md), for the moderate growth of theta functions

## Sources

- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3, TeX
  source for the complex conjugations): §1.3 (the see-saw identity (1.1)), §11.1–11.3 (theta lifts with
  $\overline{f(g)}$, the vanishing of the lower lifts and Rallis's cuspidality, the doubling see-saw and the
  isomorphism $\delta$ with $\delta(\varphi_1 \otimes \overline{\varphi_2})(0) = \langle \varphi_1, \varphi_2 \rangle$),
  §11.4, the table of ranges and Proposition 11.1 (ii) ("If the triple $(n, m, r)$ is in the convergent
  range, then one has the same identity relating the first term and the third term in (i)", proved
  from the Siegel–Weil formula in the convergent case), §11.5 (the doubling zeta integral) and
  Proposition 11.2; §2.5 (Tamagawa measures, and $\tau(H_r) = 2 = [E : F]$ for unitary groups).
- S. Rallis, "Injectivity properties of liftings associated to Weil representations", Compositio Math. 52
  (1984), 139–169, <http://www.numdam.org/item?id=CM_1984__52_2_139_0>: introduction (the inner product
  formula for symplectic–orthogonal dual pairs, the origin of the method).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a form of this result for CM extensions, with the Petersson product divided by the volume of
  $[\mathrm{U}(V)]$ and the archimedean finiteness of the doubled datum as a hypothesis, as
  `GlobalTheory.Published.RallisInnerProductConvergent`.
