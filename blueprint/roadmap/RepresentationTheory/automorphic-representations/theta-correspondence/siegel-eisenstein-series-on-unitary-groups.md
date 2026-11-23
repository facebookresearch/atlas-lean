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

1. **Convergence and continuation.** The series converges absolutely for $\operatorname{Re} s > n/2$ and
   extends to a meromorphic function of $s \in \mathbb{C}$, whose values are automorphic forms on
   $G_n(\mathbb{A})$ away from the poles.
2. **Poles** (Tan; Kudla–Rallis). If the character $x \mapsto \chi(x)\chi(\bar x)$ of $\mathbb{A}_E^\times$ is
   not of the form $x \mapsto \lvert x \rvert^{z}$ with $z \in \mathbb{C}$, then $E(s, \Phi)$ is entire. If
   $\chi(\bar x) = \chi(x)^{-1}$ for all $x$, equivalently $\chi|_{\mathbb{A}_F^\times} = \chi_E^{\kappa}$ with
   $\kappa \in \{0, 1\}$, then in the half-plane
   $\operatorname{Re} s > -\tfrac12$ the poles of $E(s, \Phi)$ are at most simple and lie in the set of points
   $s = \tfrac{m - n}{2}$ with $n < m \le 2n$ and $m \equiv \kappa \pmod 2$.

## Depends on

- [Meromorphic continuation of Hecke L-functions](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for unitary Hecke characters
- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for the quadratic character $\chi_E$ and the unitary group of the split skew-Hermitian space $W_n$
- [Global reciprocity law](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reciprocity-law/global-reciprocity-law.md), for the index $2$ of $F^\times \mathrm{N}_{E/F}(\mathbb{A}_E^\times)$ in $\mathbb{A}_F^\times$, which gives the equivalence of the two conditions in item 2
- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for automorphic forms on $G_n(\mathbb{A})$

## Proof depends on

- [Eisenstein series and their meromorphic continuation](../automorphic-forms-on-reductive-groups/eisenstein-series.md), for the convergence of Eisenstein series in a cone, their meromorphic continuation, their constant terms along the Siegel parabolic subgroup and the fact that their values are automorphic forms
- [Meromorphic continuation of Hecke L-functions](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for the Hecke L-functions of $\chi|_{\mathbb{A}_F^\times} \chi_E^{j}$ that normalize the intertwining operator in the constant term, whose poles and non-vanishing locate the poles in item 2
- [Jacquet modules of the Weil representation and degenerate principal series](jacquet-modules-of-the-weil-representation.md), for the structure of the local degenerate principal series $I_n(s, \chi_v)$ and the normalized intertwining operators used by Kudla–Rallis and Tan

## Sources

- S. Yamana, "The Siegel–Weil formula for unitary groups", Pacific J. Math. 264 (2013), 235–257,
  <https://doi.org/10.2140/pjm.2013.264.235>: introduction (absolute convergence for
  $\operatorname{Re} s > \delta n / 2$ and meromorphic continuation, for holomorphic sections), Theorem 1
  (the poles; "proven in [Tan 1999] when $\delta = 1$", the case $D = E$ used here, where the set is
  $\{(n - j)/2 : 0 \le j < n,\ \chi^0 = \epsilon_{E/F}^{j}\}$, and $j = 2n - m$), and the notation section (the
  realization of $I(s, \chi)$ by the functions with $f(m(a)n(b)g) = \chi(\nu(a))\alpha_E(\nu(a))^{s + n'/2} f(g)$).
- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3):
  §2.3 (the split space $W_n$ and $Q(Y_n)$), §6.1 (Siegel Eisenstein series of standard sections,
  meromorphic continuation, Proposition 6.1, "due to Kudla-Rallis [KR3] and V. Tan [T2]", and the
  Laurent coefficients viewed as maps $I_n^n(s, \chi) \to \mathcal{A}(G_n)$ to automorphic forms).
- V. Tan, "Poles of Siegel Eisenstein series on U(n, n)", Canad. J. Math. 51 (1999), 164–175, and
  S. S. Kudla and S. Rallis, "Poles of Eisenstein series and L-functions", Israel Math. Conf. Proc. 3
  (1990), 81–110, the original proofs, as cited by Yamana and by Gan, Qiu and Takeda.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states related results for CM extensions as `GlobalTheory.Published.SiegelEisensteinContinuation`
  (continuation and finite order of the poles) and `GlobalTheory.Published.SiegelEisensteinSimplePole`
  (simple poles), and uses a form of item 1 through `GlobalTheory.ThK.Dbl.EisBL`.
