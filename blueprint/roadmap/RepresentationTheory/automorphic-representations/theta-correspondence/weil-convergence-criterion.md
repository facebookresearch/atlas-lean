# Weil's convergence criterion for theta integrals

Let $F$ be a number field, $E/F$ a quadratic extension, $W_n$ a split skew-Hermitian space of dimension
$2n$ over $E$, and $V$ a Hermitian space of dimension $m$ and Witt index $r$ over $E$. Let $\omega$ be the
[Weil representation](weil-representation-of-unitary-dual-pairs.md) of
$\mathrm{U}(W_n)(\mathbb{A}) \times \mathrm{U}(V)(\mathbb{A})$ on $\mathcal{S}(Y_n^* \otimes_E V)(\mathbb{A})$
attached to $(\psi, \chi_V)$, and $\theta(\varphi)(g, h)$ its automorphic realization. Then the theta
integral

$$I(\varphi)(g) = \int_{\mathrm{U}(V)(F) \backslash \mathrm{U}(V)(\mathbb{A})} \theta(\varphi)(g, h)\, dh,$$

taken for the Haar measure for which $\mathrm{U}(V)(F) \backslash \mathrm{U}(V)(\mathbb{A})$ has volume $1$,
converges absolutely for every $\varphi \in \mathcal{S}(Y_n^* \otimes_E V)(\mathbb{A})$ and every $g$ if and
only if

$$r = 0 \qquad \text{or} \qquad m - r > n.$$

This is Weil's convergent range; when it holds, $I(\varphi)$ is an automorphic form on
$\mathrm{U}(W_n)(\mathbb{A})$. If $m > 2n$, every $V$ is in the range, since $r \le m/2$.

## Depends on

- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for $\omega$, its Schrödinger model and $\theta(\varphi)$
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the finite volume of $\mathrm{U}(V)(F) \backslash \mathrm{U}(V)(\mathbb{A})$

## Proof depends on

- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the Siegel sets of $\mathrm{U}(V)(\mathbb{A})$ on which Weil's convergence criteria (his §§9–11) estimate the theta function
- [Global Weil representation and theta functions](global-weil-representation-and-theta-functions.md), for the theta distribution and the moderate growth of $\theta(\varphi)$ in $g$

## Sources

- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3):
  §3.1 ("By Weil [We1], it is known that the above integral converges if and only if $r = 0$ or
  $m - r = m_0 + r > d(n)$", with $d(n) = n$ for unitary groups, and the normalization of the measure),
  §3.6 (when $m > 2 d(n)$ one is automatically in the convergent range), and §2.3 (the split space $W_n$
  of dimension $2n$).
- S. Yamana, "On the Siegel–Weil formula: the case of singular forms", Compositio Math. 147 (2011),
  1003–1021, <https://doi.org/10.1112/S0010437X11005379>: §1.3, the convergence of the theta integral for
  all $\Phi$ when $\phi$ is anisotropic or $m - r > \varrho$ ($\varrho = n$ in the unitary case 2).
- A. Weil, "Sur la formule de Siegel dans la théorie des groupes classiques", Acta Math. 113 (1965),
  1–87, <https://doi.org/10.1007/BF02391774>: §§9–11 (convergence criteria for integrals over
  $G_k \backslash G_{\mathbb{A}}$ resting on reduction theory), the source GQT cite.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the convergence for $n \ge 1$ as `GlobalTheory.Published.WeilThetaConvergence`.
