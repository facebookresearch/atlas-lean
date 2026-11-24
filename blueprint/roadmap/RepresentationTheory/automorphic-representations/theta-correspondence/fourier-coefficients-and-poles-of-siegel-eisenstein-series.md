# Fourier coefficients and poles of Siegel Eisenstein series

This node is still to be broken down. It covers the analytic inputs of the proofs of Kudla–Rallis and
Tan that bound the poles of
[Siegel Eisenstein series on unitary groups](siegel-eisenstein-series-on-unitary-groups.md). Let
$G_n = \mathrm{U}(W_n)$ with $W_n$ split of dimension $2n$ over a quadratic extension $E/F$ of number fields,
$Q = MN$ the Siegel parabolic subgroup, $N \cong \mathrm{Her}_n$ the Hermitian matrices, $\chi$ a Hecke
character of $\mathbb{A}_E^\times / E^\times$ with $\chi|_{\mathbb{A}_F^\times} = \chi_E^\kappa$, $I_n(s, \chi)$ the representation of
$G_n(\mathbb{A})$ obtained by unnormalized induction from the character $\chi(\det a) \lvert \det a \rvert_E^{s + n/2}$ of the Levi
factor of $Q$ (equivalently, normalized induction of $\chi(\det a) \lvert \det a \rvert_E^{s}$), $E(s, \Phi)$ the Eisenstein series of a
holomorphic section $\Phi$, and $S_0$ a finite set of places containing the archimedean places and the places
where $E$, $\chi$ or a given decomposable section $\Phi = \otimes_v \Phi_v$ is ramified.

- **Normalized series and intertwining operators.** The normalizing factor $b^*_n(s)$, a product of
  partial Hecke $L$-functions $L^{S_0}(2s + j, \chi|_{\mathbb{A}_F^\times} \chi_E^{j+n})$ over $1 \le j \le n$, the normalized
  series $E^*(s, \Phi) = b^*_n(s) E(s, \Phi)$ of Tan, and the holomorphy of the normalized local intertwining
  operators $M^*(s, \chi_v)$ at all places (including the split ones).
- **Non-singular Fourier coefficients.** For $\beta \in \mathrm{Her}_n(F)$ with $\det \beta \ne 0$ and a decomposable
  section $\Phi = \otimes_v \Phi_v$, the $\beta$-th Fourier coefficient of $E(s, \Phi)$ along $N$ is the product of the local
  Siegel–Whittaker integrals of the $\Phi_v$ (with compatible measures); for a general holomorphic section it is the
  corresponding sum of such products, by linearity. The non-singular coefficients of the normalized series $E^*$
  are holomorphic in $\operatorname{Re} s > 0$ (Tan's Lemma 4.2). At a point $s_1$ with $\operatorname{Re} s_1 > 0$ outside the set of
  candidate poles, Tan chooses a place where the relevant local constituent is irreducible and non-singular; a
  leading Laurent coefficient at $s_1$ all of whose non-singular coefficients vanish would give an injective map
  from that constituent into singular forms, so there is no pole there (his Proposition 4.1, with a separate
  argument at $s = 0$). At the candidate poles the residue may be singular: for $n = 1$, $\chi = 1$, $F = \mathbb{Q}$ and the
  spherical section, the residue at $s = \tfrac12$ is a non-zero constant, with all non-singular coefficients zero.
- **Induction on the rank and functional equation.** The constant term along the parabolic subgroup
  stabilizing an isotropic line, expressed through Siegel Eisenstein series of $G_{n-1}$, bounds by induction the
  order of the poles at the candidate points in $\operatorname{Re} s > 0$ by $1$ (Tan's Proposition 4.4); the functional equation of
  $E^*$ transfers the result to $\operatorname{Re} s < 0$ (Proposition 4.8).

A good expansion has pages for the normalizing factors and the normalized local intertwining operators,
for the Euler product of the non-singular Fourier coefficients and the holomorphy of their normalized
local factors, for the constant term along the line parabolic subgroup, and for the functional equation,
each with a precise statement and the sources below; Tan's paper assumes $F$ totally real, and the
general case should be sourced from Kudla–Rallis or from a published account covering all number fields.

## Depends on

- [Eisenstein series and their meromorphic continuation](../automorphic-forms-on-reductive-groups/eisenstein-series.md), for Eisenstein series induced from the Siegel parabolic subgroup, their intertwining operators and constant terms
- [Meromorphic continuation of Hecke L-functions](../../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for the Hecke $L$-functions in the normalizing factors
- [Jacquet modules of the Weil representation and degenerate principal series](jacquet-modules-of-the-weil-representation.md), for the local degenerate principal series $I_n(s, \chi_v)$ and their constituents

## Proof depends on

- [Eisenstein series and their meromorphic continuation](../automorphic-forms-on-reductive-groups/eisenstein-series.md), for the intertwining operators and the functional equation, which Tan applies to the normalized series (Proposition 4.8); the constant term formula there is for cuspidal Levi data, and $\chi \circ \det$ on $\mathrm{GL}_n$, $n > 1$, is not cuspidal, so the recursion along the line parabolic subgroup behind Proposition 4.4 is Tan's own computation
- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for the decomposition of $G_n(F)$ into $Q(F)$-double cosets, after which a non-degenerate $\beta$ kills all but the open cell and the Fourier coefficient of a factorizable section is a product of local integrals

## Sources

- V. Tan, "Poles of Siegel Eisenstein series on U(n, n)", Canad. J. Math. 51 (1999), 164–175,
  <https://doi.org/10.4153/CJM-1999-010-4>: the Main Theorem (for the normalized series), (2.3) (the local
  normalizing factors), §3, p. 171 and (3.1) (Fourier coefficients of decomposable sections as products of
  local integrals), Proposition 4.1 (no pole off the candidate set, by an irreducible non-singular local
  constituent), Lemma 4.2 (non-singular coefficients of the normalized series holomorphic in $\operatorname{Re} s > 0$),
  Proposition 4.4 (at most simple poles at the candidate points, by induction through the line parabolic
  subgroup), Lemma 4.6 and Proposition 4.8 ($\operatorname{Re} s < 0$), pp. 172–175; $F$ is assumed totally real.
- M. P. Young, "Explicit calculations with Eisenstein series", arXiv:1710.03624 (version 2): §4.1 and
  Proposition 4.1 (the constant residue of the classical Eisenstein series, for the example).
- S. Yamana, "The Siegel–Weil formula for unitary groups", Pacific J. Math. 264 (2013), 235–257,
  <https://doi.org/10.2140/pjm.2013.264.235>: §1, Lemma 1.2 (the normalized intertwining operator $M^*(s, \chi)$
  is entire, at inert and split places) and §2.
- S. S. Kudla and S. Rallis, "Poles of Eisenstein series and L-functions", Israel Math. Conf. Proc. 3
  (1990), 81–110, as cited by Gan–Qiu–Takeda (§6.1) for the poles of Siegel Eisenstein series.
