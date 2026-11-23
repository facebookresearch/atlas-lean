# Fourier coefficients and poles of Siegel Eisenstein series

This node is still to be broken down. It covers the analytic inputs of the proofs of Kudla–Rallis and
Tan that bound the poles of
[Siegel Eisenstein series on unitary groups](siegel-eisenstein-series-on-unitary-groups.md). Let
$G_n = \mathrm{U}(W_n)$ with $W_n$ split of dimension $2n$ over a quadratic extension $E/F$ of number fields,
$Q = MN$ the Siegel parabolic subgroup, $N \cong \mathrm{Her}_n$ the Hermitian matrices, $\chi$ a Hecke
character of $\mathbb{A}_E^\times / E^\times$ with $\chi|_{\mathbb{A}_F^\times} = \chi_E^\kappa$, $I_n(s, \chi)$ the representation of
$G_n(\mathbb{A})$ induced from the character $\chi(\det a) \lvert \det a \rvert_E^{s + n/2}$ of the Levi factor of $Q$, and
$E(s, \Phi)$ the Eisenstein series of a holomorphic section $\Phi$.

- **Normalized series and intertwining operators.** The normalizing factor $b^*_n(s)$, a product of
  partial Hecke $L$-functions $L^S(2s + j, \chi|_{\mathbb{A}_F^\times} \chi_E^{j+n})$ over $1 \le j \le n$, the normalized
  series $E^*(s, \Phi) = b^*_n(s) E(s, \Phi)$ of Tan, and the holomorphy of the normalized local intertwining
  operators $M^*(s, \chi_v)$ at all places (including the split ones).
- **Non-singular Fourier coefficients.** For $\beta \in \mathrm{Her}_n(F)$ with $\det \beta \ne 0$, the $\beta$-th
  Fourier coefficient of $E(s, \Phi)$ along $N$ is an Euler product of local Siegel–Whittaker integrals; after
  normalization these coefficients are holomorphic in the relevant region, and a leading Laurent
  coefficient of $E^*$ all of whose non-singular coefficients vanish is ruled out by local irreducibility and
  non-singularity of the relevant constituents of the degenerate principal series.
- **Induction on the rank and functional equation.** The constant term along the parabolic subgroup
  stabilizing an isotropic line, expressed through Siegel Eisenstein series of $G_{n-1}$, gives by induction
  that the poles in $\operatorname{Re} s > 0$ are at most simple; the functional equation of $E^*$ transfers the
  result to $\operatorname{Re} s < 0$.

A good expansion has pages for the normalizing factors and the normalized local intertwining operators,
for the Euler product of the non-singular Fourier coefficients and the holomorphy of their normalized
local factors, for the constant term along the line parabolic subgroup, and for the functional equation,
each with a precise statement and the sources below; Tan's paper assumes $F$ totally real, and the
general case should be sourced from Kudla–Rallis or from a published account covering all number fields.

## Depends on

- [Eisenstein series and their meromorphic continuation](../automorphic-forms-on-reductive-groups/eisenstein-series.md), for Eisenstein series induced from the Siegel parabolic subgroup, their intertwining operators and constant terms
- [Meromorphic continuation of Hecke L-functions](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for the Hecke $L$-functions in the normalizing factors
- [Jacquet modules of the Weil representation and degenerate principal series](jacquet-modules-of-the-weil-representation.md), for the local degenerate principal series $I_n(s, \chi_v)$ and their constituents

## Sources

- V. Tan, "Poles of Siegel Eisenstein series on U(n, n)", Canad. J. Math. 51 (1999), 164–175,
  <https://doi.org/10.4153/CJM-1999-010-4>: the Main Theorem (for the normalized series), (2.3) (the local
  normalizing factors), §3 (Fourier coefficients), Proposition 4.1, Lemma 4.2 (non-singular Fourier
  coefficients), Proposition 4.4 (simple poles in $\operatorname{Re} s > 0$, by induction), Lemma 4.6 and
  Proposition 4.8 ($\operatorname{Re} s < 0$); $F$ is assumed totally real.
- S. Yamana, "The Siegel–Weil formula for unitary groups", Pacific J. Math. 264 (2013), 235–257,
  <https://doi.org/10.2140/pjm.2013.264.235>: §1, Lemma 1.2 (the normalized intertwining operator $M^*(s, \chi)$
  is entire, at inert and split places) and §2.
- S. S. Kudla and S. Rallis, "Poles of Eisenstein series and L-functions", Israel Math. Conf. Proc. 3
  (1990), 81–110, as cited by Gan–Qiu–Takeda (§6.1) for the poles of Siegel Eisenstein series.
