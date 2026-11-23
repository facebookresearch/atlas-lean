# Siegel–Weil formula for unitary groups in Weil's convergent range

Let $F$, $E$, $\chi_E$, $W_n = Y_n \oplus Y_n^*$, $G_n = \mathrm{U}(W_n)$ and $I_n(s, \chi)$ be as for the
[Siegel Eisenstein series](siegel-eisenstein-series-on-unitary-groups.md). Let $V$ be a Hermitian space
over $E$ of dimension $m$ and Witt index $r$, $H = \mathrm{U}(V)$, $\psi$ a non-trivial character of
$\mathbb{A}_F / F$, $\chi_V$ a Hecke character of $\mathbb{A}_E^\times / E^\times$ with
$\chi_V|_{\mathbb{A}_F^\times} = \chi_E^{m}$, and $\omega$ the
[Weil representation](weil-representation-of-unitary-dual-pairs.md) of
$G_n(\mathbb{A}) \times H(\mathbb{A})$ on $\mathcal{S}((Y_n^* \otimes_E V)(\mathbb{A}))$ attached to
$(\psi, \chi_V)$, with theta function $\theta(g, h; \varphi) = \sum_{x \in (Y_n^* \otimes_E V)(F)} \omega(g, h)\varphi(x)$.
Let $\varphi$ correspond to a polynomial in the Fock model at every archimedean place of $F$. Put
$s_0 = \tfrac{m - n}{2}$, write $g = m(a) u k$ with $u \in N(\mathbb{A})$ and $k \in K$, and let
$\lvert a(g) \rvert = \lvert \det a \rvert_{\mathbb{A}_E}$. Then
$f_\varphi^{(s)}(g) = \lvert a(g) \rvert^{s - s_0}\, \omega(g)\varphi(0)$ is a standard section of
$I_n(s, \chi_V)$, the Siegel–Weil section of $\varphi$.

Suppose that $V$ is in [Weil's convergent range](weil-convergence-criterion.md): $r = 0$ or $m - r > n$.
Then $E(s, f_\varphi)$ is holomorphic at $s = s_0$, and for every $g \in G_n(\mathbb{A})$

$$E(s_0, f_\varphi)(g) = \kappa \int_{H(F) \backslash H(\mathbb{A})} \theta(g, h; \varphi)\, dh, \qquad \kappa = \begin{cases} 2 & \text{if } m \le n, \\ 1 & \text{if } m > n, \end{cases}$$

where $dh$ is the Haar measure for which $H(F) \backslash H(\mathbb{A})$ has volume $1$. In the convergent
range $m \le n$ forces $r = 0$.

The formula is due to Weil for $m > 2n$, when the Eisenstein series converges absolutely at $s_0$, to
Ichino for $n < m \le 2n$, and to Yamana for $m \le n$.

## Depends on

- [Siegel Eisenstein series on unitary groups](siegel-eisenstein-series-on-unitary-groups.md), for $I_n(s, \chi_V)$, standard sections and $E(s, f)$ with its meromorphic continuation
- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for $\omega$, its formulas on the Siegel parabolic subgroup, which make $g \mapsto \omega(g)\varphi(0)$ an element of $I_n(s_0, \chi_V)$, and the Fock model at the archimedean places
- [Global Weil representation and theta functions](global-weil-representation-and-theta-functions.md), for the theta function
- [Weil's convergence criterion for theta integrals](weil-convergence-criterion.md), for the convergence of the theta integral

## Proof depends on

- [Weil's convergence criterion for theta integrals](weil-convergence-criterion.md), for the absolute convergence that allows the Fourier coefficients of the theta integral along $N$ to be computed termwise
- [Eisenstein series and their meromorphic continuation](../automorphic-forms-on-reductive-groups/eisenstein-series.md), for the Fourier coefficients and constant terms of Siegel Eisenstein series, which the proofs compare with those of the theta integral (Ichino's Proposition 6.2 for the non-singular coefficients)
- [Siegel Eisenstein series on unitary groups](siegel-eisenstein-series-on-unitary-groups.md), for the poles being at most simple, so that holomorphy at $s_0$ amounts to the vanishing of the residue map
- [Jacquet modules of the Weil representation and degenerate principal series](jacquet-modules-of-the-weil-representation.md), for the local degenerate principal series: the invariant distribution theorem (Mœglin–Vignéras–Waldspurger, Lee–Zhu) through which the residue map factors through the maximal $H(F_w)$-invariant quotient $R(V_w, \chi_{V_w})$ of the local Weil representation, the irreducibility of that quotient at a finite place (Kudla–Sweet) and its archimedean analogue (Ichino)
- [Local–global principle for Hermitian spaces over a quadratic extension](../../../NumberTheory/quadratic-forms-sums-of-squares/hermitian-local-global-principle.md), for the local–global principle behind the existence of a place $w$ inert in $E$ at which the Witt index of $V_w$ is at most $r$, used in the proof of holomorphy (Scharlau, Theorem 10.6.2, as cited by Yamana)

## Sources

- S. Yamana, "The Siegel–Weil formula for unitary groups", Pacific J. Math. 264 (2013), 235–257,
  <https://doi.org/10.2140/pjm.2013.264.235>: introduction, the definitions of the theta function, of
  $S(V^n(A))$ (functions corresponding to polynomials in the Fock model at every archimedean place), of
  $f^{(s)}_\Phi$ and of $\lvert a(g) \rvert$ (notation section), Weil's criterion, and Theorem 2 ("If
  $m \le n$ or if $m - r > n$, then for all $\Phi$ ... $E(g; f^{(s)}_\Phi)$ is holomorphic at $s = s_0$ and
  $E(g; f^{(s)}_\Phi)|_{s = s_0} = \varkappa I(g; \Phi)$", $\varkappa = 2$ if $m \le n$, $1$ if $m - r > n$), in
  the case $\delta = 1$, where it was "proven in [Weil 1965] if $m > 2n$, and in [Tan 1998; Ichino 2004;
  2007; Yamana 2011]"; the remark after Theorem 2 on the local facts used; §3, Lemma 3.1 and the proof
  of Theorem 2 in the case $m - r > n$ (the place $w$, the invariant distribution theorem, Kudla–Sweet's
  irreducibility, and the reduction to Section 3 of Ichino's paper).
- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3):
  §3.1 (the theta integral, normalized so that $[H]$ has volume $1$, "the convention used in [KR1, KR2,
  Ik, I1, I2, I3, Y2]"), §2.5 ($\tau(H_r) = 2$ for unitary groups), §6.2 (Siegel–Weil sections),
  Theorem 7.1 (the anisotropic case, $c_{m,n} = 1$ if $s_{m,n} > 0$ and $2$ otherwise,
  $\tau(H_0) / [E : F] = 1$ for unitary groups) with the attributions after it (Weil for $m > 2d(n)$; A.
  Ichino, Math. Z. 255 (2007), 721–729, for $d(n) < m \le 2 d(n)$; S. Yamana, Compositio Math. 147 (2011),
  1003–1021, for $m \le d(n)$), and the proof of Proposition 11.1 (ii) (the isotropic convergent case,
  from Kudla–Rallis and Ichino).
- S. Yamana, "On the Siegel–Weil formula: the case of singular forms", Compositio Math. 147 (2011),
  1003–1021, <https://doi.org/10.1112/S0010437X11005379>: introduction and Theorem 2.2 (the unitary case
  2, with $\varrho = n$, $s_0 = (m - n)/2$, $\kappa = 2$ for $m \le \varrho$).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states forms of this result for CM extensions as `GlobalTheory.Published.WeilSiegelFormulaUnitary`
  ($m > 2n$), `GlobalTheory.Published.SiegelWeilUnitaryConvergent` and
  `GlobalTheory.Published.SiegelWeilUnitarySchrodinger` ($n < m \le 2n$, $m - r > n$), and
  `GlobalTheory.ThK.Dbl.SiegelWeilStd` (definite spaces, with the factor $2$ when $m \le n$).
