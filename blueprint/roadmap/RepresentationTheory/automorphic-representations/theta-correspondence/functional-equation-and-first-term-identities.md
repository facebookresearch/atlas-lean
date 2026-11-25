# Functional equation and first-term identities for Siegel Eisenstein series

This node is still to be broken down. It covers the inputs of the proof of the
[Siegel–Weil formula](siegel-weil-formula-convergent-range.md) for anisotropic Hermitian spaces $V$ of
dimension $m$ with $0 < m \le n$, where the Siegel–Weil point $s_0 = \tfrac{m-n}{2}$ is $\le 0$. Let $G_n = \mathrm{U}(W_n)$ with
$W_n$ split of dimension $2n$, $I_n(s, \chi_V)$ the degenerate principal series, $E(s, f)$ the
[Siegel Eisenstein series](siegel-eisenstein-series-on-unitary-groups.md) of a holomorphic section $f$, and
$I_V(\varphi)$ the (convergent) theta integral of $V$, for Schwartz functions $\varphi$ that correspond to polynomials in the
Fock model at every archimedean place (Yamana's test class, his §1.3), with Siegel–Weil sections $f_\varphi$. The two cases
$m < n$ and $m = n$ have different proofs.

- **Functional equation and the zero at $s_0$ ($0 < m < n$).** The global intertwining operator
  $M(s) \colon I_n(s, \chi_V) \to I_n(-s, \chi_V)$, meromorphic, with $E(s, f) = E(-s, M(s) f)$; Yamana's scalar functions
  $a(s)$ and $b(s)$ (products of Hecke $L$-functions) and the normalized operator $M^\circ(s) = (b(s)/a(s)) M(s)$, for
  which $E(s, f(s)) = (a(s)/b(s))\, E(-s, h(-s))$ with $h(-s) = M^\circ(s) f(s)$. In the unitary case the factor $a(s)/b(s)$ has a
  simple zero at $s_0$. For a standard section $f$ with $f(s_0)$ in the image $\Pi(V)$ of the Siegel–Weil sections of $V$
  (or of a coherent collection of local spaces), the section $h(t) = M^\circ(-t) f(-t)$ of $I_n(t, \chi_V)$ is holomorphic at
  $t = -s_0$ (Yamana's Proposition 3.1: $\gamma(t) h(t)$ is holomorphic for an entire $\gamma$ with $\gamma(-s_0) \ne 0$), equivalently
  $M^\circ(s) f(s)$ is regular at $s = s_0$; and $E(t, h(t))$ has at most a simple pole at $t = -s_0$. Hence
  $E(s_0, f) = -\gamma \,\mathrm{Res}_{t = -s_0} E(t, h(t))$ for an explicit non-zero constant $\gamma$ (Yamana's (4.1)). This is not a statement
  that the normalized operator vanishes on arbitrary data in $I_n(s_0, \chi_V)$, nor merely a holomorphy statement for
  the operator at a positive input.
- **First-term identity ($0 < m < n$).** Let $V' = V \oplus \mathbb{H}^{n-m}$, of dimension $2n - m$, and $\Pi(V')$ the image of
  its Siegel–Weil sections in $I_n(-s_0, \chi_V)$. For a holomorphic section $f$ with $f(-s_0) \in \Pi(V')$, the operator
  $M^\circ(-s_0)$ maps $\Pi(V')$ onto the image $\Pi(V)$ of the Siegel–Weil sections of $V$ in $I_n(s_0, \chi_V)$; if
  $M^\circ(-s_0) f(-s_0) = f_\varphi(s_0)$ with $\varphi$ a Schwartz function for $V$, then
  $\mathrm{Res}_{t = -s_0} E(t, f) = c_0\, I_V(\varphi)$ for a non-zero constant $c_0$ independent of $f$ (Yamana's
  Proposition 5.1 and Theorem 5.2). The right side is the ordinary theta integral of the smaller anisotropic
  space $V$, not a theta integral of $V'$ (which is outside Weil's convergent range, since $\dim V' - r_{V'} = n$).
  Combined with the functional equation this makes $E(s_0, f_\varphi)$ proportional to $I_V(\varphi)$ (Corollary 5.4).
- **The constant $2$ ($0 < m < n$).** Comparison of the Fourier coefficients of rank $m$ (Yamana 2011, §6:
  $\beta = \mathrm{diag}(0, \beta_1)$, reduction to the smaller group and the known non-zero central value), which shows that
  the proportionality constant is $2$; the residue constant $c_0$ is a different number.
- **The central case $m = n$.** Here $s_0 = 0$, the Siegel Eisenstein series is holomorphic at $0$ by the pole
  theorem for $\operatorname{Re} s \ge 0$, and there is no residue at an opposite point. The identity
  $E(0, f_\varphi) = 2 I_V(\varphi)$ is Ichino's (Yamana 2011, Proposition 5.8 (i)); Yamana 2013 obtains it from the
  global multiplicity bound $\dim \mathrm{Hom}_{G_n(\mathbb{A})}(\Pi, \mathcal{A}(G_n)) \le 1$ for the relevant constituent $\Pi$ (zero for
  incoherent collections; his Proposition 3.2), Lemmas 2.1 (2) and 3.1, and a comparison of non-singular
  Fourier coefficients of rank $n$.
- **Local structure.** The local images $R_n(V_v)$ as submodules of $I_n(s_0, \chi_{V,v})$, the small module as a
  quotient of the larger-space module at $-s_0$, and the multiplicity-freeness of $K$-types used in Corollary 5.4
  (Yamana 2011, Proposition 5.1 and Remark 5.3 (iii); 2013, Propositions 1.4, 3.3 and 3.5); these local facts
  are distinct from the global multiplicity bound above.

A good expansion has pages for the global intertwining operator, the functional equation and the zero of
$a/b$ at $s_0$; for the first-term identity with its matching condition; for the rank-$m$ comparison giving the
constant $2$; for the central case $m = n$ with the global multiplicity bound; and for the local structure of
the degenerate principal series used, each with a precise statement and the sources below.

## Depends on

- [Siegel Eisenstein series on unitary groups](siegel-eisenstein-series-on-unitary-groups.md), for $I_n(s, \chi_V)$, standard sections and $E(s, \Phi)$
- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for Siegel–Weil sections
- [Jacquet modules of the Weil representation and degenerate principal series](jacquet-modules-of-the-weil-representation.md), for the local structure of the degenerate principal series
- [Weil's convergence criterion for theta integrals](weil-convergence-criterion.md), for the theta integral $I_V(\varphi)$ of the anisotropic space $V$ and its normalization, which the statements use

## Proof depends on

- [Fourier coefficients and poles of Siegel Eisenstein series](fourier-coefficients-and-poles-of-siegel-eisenstein-series.md), for the non-singular Fourier coefficients compared in the central case and, after reduction to a smaller group, in the rank-$m$ comparison (Yamana 2013, Lemmas 2.1 (2) and 3.1, Proposition 3.2; Yamana 2011, §6); the equality with the coefficients of the theta integral is a further step
- [Eisenstein series and their meromorphic continuation](../automorphic-forms-on-reductive-groups/eisenstein-series.md), for the meromorphic global intertwining operator and the functional equation, before Yamana's normalization $M^\circ(s)$
- [Meromorphic continuation of Hecke L-functions](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for the completed Hecke $L$-functions in $a(s)$ and $b(s)$
- [Weil's convergence criterion for theta integrals](weil-convergence-criterion.md), for the convergence of $I_V(\varphi)$ for anisotropic $V$

## Sources

- S. Yamana, "On the Siegel–Weil formula: the case of singular forms", Compositio Math. 147 (2011),
  1003–1021, <https://doi.org/10.1112/S0010437X11005379>: §1.2 (the meromorphic family and the
  functional equation), §1.3 (the test functions corresponding to polynomials in the Fock model), §3, Proposition 3.1
  (the normalized intertwining operator), §4, (4.1) (with $h(-s) = M^\circ(s) f(s)$, $a(s)/b(s)$ and its simple zero;
  the case $m = n$ excluded), §5, Proposition 5.1, Theorem 5.2 (after Ichino, Jiang–Soudry and Kudla–Rallis;
  $\mathrm{Res}_{t=-s_0} E(t, f) = c_0 I_V(\varphi)$ under $M^\circ(-s_0) f(-s_0) = f_\varphi(s_0)$), Remark 5.3 (iii), Corollary 5.4,
  Proposition 5.8 (i) (the case $m = n$, after A. Ichino, "A regularized Siegel-Weil formula for unitary
  groups", Math. Z. 247 (2004), Theorem 4.2) and §6 (the constant of proportionality, pp. 1017–1019), in the
  unitary case 2.
- S. Yamana, "The Siegel–Weil formula for unitary groups", Pacific J. Math. 264 (2013), 235–257,
  <https://doi.org/10.2140/pjm.2013.264.235>: Proposition 1.4, Lemmas 2.1 (2) and 3.1, §3, Proposition 3.2 (the
  global multiplicity bound), Propositions 3.3 and 3.5 and Theorem 3.7 (the case $m < n$, with the same matching
  condition and right side on $V$).
