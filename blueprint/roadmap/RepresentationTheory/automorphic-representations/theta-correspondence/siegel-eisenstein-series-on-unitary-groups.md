# Siegel Eisenstein series on unitary groups

Let $F$ be a number field, $E/F$ a quadratic extension with non-trivial automorphism $x \mapsto \bar x$,
and $\chi_E$ the quadratic character of $\mathbb{A}_F^\times / F^\times$ attached to $E/F$. Let $W_n$ be a
skew-Hermitian space of dimension $2n$ over $E$ with a polarization $W_n = Y_n \oplus Y_n^*$ by maximal
isotropic subspaces of dimension $n$, $G_n = \mathrm{U}(W_n)$, and $Q = Q(Y_n) = MN$ the Siegel
parabolic subgroup stabilizing $Y_n$, with Levi factor
$M = \{m(a) : a \in \mathrm{GL}(Y_n)\} \cong \mathrm{Res}_{E/F} \mathrm{GL}_n$. Let $K = \prod_v K_v$ be the
standard maximal compact subgroup of $G_n(\mathbb{A})$, $\lvert\cdot\rvert$ the norm of
$\mathbb{A}_E^\times$, and $\chi$ a unitary
[Hecke character](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md)
of $\mathbb{A}_E^\times / E^\times$. The degenerate principal series
$I_n(s, \chi) = \mathrm{Ind}_{Q(\mathbb{A})}^{G_n(\mathbb{A})} (\chi \circ \det) \lvert \det \rvert^s$ (normalized
induction) is the space of right $K$-finite functions $\Phi$ on $G_n(\mathbb{A})$ with
$\Phi(m(a) u g) = \chi(\det a)\, \lvert \det a \rvert^{s + n/2}\, \Phi(g)$ for $a \in \mathrm{GL}_n(\mathbb{A}_E)$,
$u \in N(\mathbb{A})$ and $g \in G_n(\mathbb{A})$. A section $s \mapsto \Phi_s \in I_n(s, \chi)$ is standard if
its restriction to $K$ does not depend on $s$, and holomorphic if it is a holomorphic family. The Siegel
Eisenstein series of a holomorphic section is

$$E(s, \Phi)(g) = \sum_{\gamma \in Q(F) \backslash G_n(F)} \Phi_s(\gamma g), \qquad g \in G_n(\mathbb{A}).$$

Let $n \ge 1$.

1. **Convergence and continuation.** The series converges absolutely for $\operatorname{Re} s > n/2$ and
   extends to a meromorphic function of $s \in \mathbb{C}$, whose values are automorphic forms on
   $G_n(\mathbb{A})$ away from the poles.
2. **Poles in the right half-plane** (Kudla–Rallis; Tan). Suppose that $\chi(\bar x) = \chi(x)^{-1}$ for all $x$,
   equivalently $\chi|_{\mathbb{A}_F^\times} = \chi_E^{\kappa}$ with $\kappa \in \{0, 1\}$. Then for $\operatorname{Re} s \ge 0$,
   $E(s, \Phi)$ is holomorphic except possibly at the points $s = \tfrac{m - n}{2}$ with $n < m \le 2n$ and
   $m \equiv \kappa \pmod 2$, where it has at most simple poles; in particular it is holomorphic at $s = 0$.

No assertion is made in $\operatorname{Re} s < 0$, where the poles of this (unnormalized) series also come from
zeros of Hecke $L$-functions: for $F = \mathbb{Q}$, $n = 1$, $\chi = 1$ and the spherical section, the restriction to
$\mathrm{SL}_2$ is the classical Eisenstein series with parameter $s + \tfrac12$, whose constant term involves
$\Lambda(2s)/\Lambda(2s+1)$ for the completed Riemann zeta function $\Lambda$, so that every non-trivial zero $\rho$ of
$\zeta$ gives a pole at $s = (\rho - 1)/2$. Tan's theorem for $\operatorname{Re} s < 0$ concerns the series normalized by
a product of Hecke $L$-functions.

## Depends on

- [Meromorphic continuation of Hecke L-functions](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for unitary Hecke characters
- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for the quadratic character $\chi_E$ and the unitary group of the split skew-Hermitian space $W_n$
- [Global reciprocity law](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reciprocity-law/global-reciprocity-law.md), for the index $2$ of $F^\times \mathrm{N}_{E/F}(\mathbb{A}_E^\times)$ in $\mathbb{A}_F^\times$, which gives the equivalence of the two conditions in item 2
- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for automorphic forms on $G_n(\mathbb{A})$

## Proof depends on

- [Eisenstein series and their meromorphic continuation](../automorphic-forms-on-reductive-groups/eisenstein-series.md), for the convergence of Eisenstein series in a cone, their meromorphic continuation and their constant terms along the Siegel parabolic subgroup (item 1); the inducing data $\chi \circ \det$ on $\mathrm{GL}_n$, $n > 1$, are not cuspidal, so the automorphy of the values away from the poles is taken from the specific statements of Yamana and of Gan–Qiu–Takeda for Siegel Eisenstein series, not from the automorphy clause for cuspidal data
- [Fourier coefficients and poles of Siegel Eisenstein series](fourier-coefficients-and-poles-of-siegel-eisenstein-series.md), for the normalized intertwining operators, the non-singular Fourier coefficients, the induction on the rank through the line parabolic subgroup and the functional equation, through which Kudla–Rallis and Tan bound the poles (item 2)
- [Meromorphic continuation of Hecke L-functions](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for the Hecke $L$-functions that normalize the intertwining operators and the series
- [Jacquet modules of the Weil representation and degenerate principal series](jacquet-modules-of-the-weil-representation.md), for the structure of the local degenerate principal series $I_n(s, \chi_v)$ used to exclude singular leading coefficients

## Sources

- S. Yamana, "The Siegel–Weil formula for unitary groups", Pacific J. Math. 264 (2013), 235–257,
  <https://doi.org/10.2140/pjm.2013.264.235>: introduction (absolute convergence for
  $\operatorname{Re} s > \delta n / 2$ and meromorphic continuation, for holomorphic sections), and the notation
  section (the realization of $I(s, \chi)$ by the functions with
  $f(m(a)n(b)g) = \chi(\nu(a))\alpha_E(\nu(a))^{s + n'/2} f(g)$), in the case $D = E$. Yamana's Theorem 1, which
  states a pole list for $\operatorname{Re} s > -\tfrac12$ for the series as written, is not used; Tan's theorem, which Yamana
  cites for it, concerns the normalized series and does not prove that statement word for word.
- M. P. Young, "Explicit calculations with Eisenstein series", arXiv:1710.03624 (version 2): §4.1 and
  Proposition 4.1 (the constant term of the classical Eisenstein series and its normalization), for the
  example above.
- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3):
  §2.3 (the split space $W_n$ and $Q(Y_n)$), §6.1 (Siegel Eisenstein series of standard sections,
  meromorphic continuation, Proposition 6.1 (for $\operatorname{Re}(s) \ge 0$, holomorphy except at the points
  $s_{m,n} > 0$ of $X_n(\chi)$, poles of order at most $1$), "due to Kudla-Rallis [KR3] and V. Tan [T2]", the
  table of Proposition 5.1 defining $X_n(\chi)$, and the
  Laurent coefficients viewed as maps $I_n^n(s, \chi) \to \mathcal{A}(G_n)$ to automorphic forms).
- V. Tan, "Poles of Siegel Eisenstein series on U(n, n)", Canad. J. Math. 51 (1999), 164–175, and
  S. S. Kudla and S. Rallis, "Poles of Eisenstein series and L-functions", Israel Math. Conf. Proc. 3
  (1990), 81–110, the original proofs, as cited by Gan, Qiu and Takeda; Tan's Main Theorem concerns the
  series normalized by the factor of his (2.3), over a totally real field $F$.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states special positive-rank, flat-section formulations for CM extensions as
  `GlobalTheory.Published.SiegelEisensteinContinuation` (continuation and finite order of the poles) and
  `GlobalTheory.Published.SiegelEisensteinSimplePole` (at most a simple pole at a specified positive point),
  and uses a form of item 1 through `GlobalTheory.ThK.Dbl.EisBL`.
