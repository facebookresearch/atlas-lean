# Shapiro's lemma for profinite groups

Let $G$ be a profinite group, $H$ a closed subgroup and $A$ a discrete $H$-module. The induced module
$\operatorname{Ind}_G^H(A)$ is the group of continuous maps $x \colon G \to A$ with $x(\tau\sigma) = \tau\, x(\sigma)$
for all $\tau \in H$, a discrete $G$-module under $(\rho x)(\sigma) = x(\sigma\rho)$; the map
$\pi \colon \operatorname{Ind}_G^H(A) \to A$, $x \mapsto x(1)$, is a homomorphism of $H$-modules. Then for every
$n \ge 0$ there is a canonical isomorphism of [cohomology](cohomology-with-discrete-coefficients.md) groups

$$
\mathrm{sh} \colon H^n(G, \operatorname{Ind}_G^H(A)) \xrightarrow{\ \sim\ } H^n(H, A),
$$

which in degree $0$ is induced by $\pi$. For $H = 1$,
$\operatorname{Ind}_G^1(A) \cong \operatorname{Ind}_G(A)$ and the statement recovers the
[acyclicity of induced modules](induced-modules-are-acyclic.md).

For abstract groups and representations, Mathlib states Shapiro's lemma for coinduction as
`groupCohomology.coindIso`, an isomorphism `groupCohomology (Rep.coind S.subtype A) n ≅ groupCohomology A n` for a
subgroup `S`; the statement here is the one for closed subgroups of profinite groups and continuous cochains.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the cohomology of $G$ and of $H$

## Proof depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  the isomorphism $X^n(G, \operatorname{Ind}_G^H(A))^G \cong X^n(G, A)^H$, $y \mapsto x$ with
  $x(\sigma_0, \dots, \sigma_n)(\sigma) = y(\sigma\sigma_0, \dots, \sigma\sigma_n)$, used in the proof
- [Induced modules are cohomologically trivial](induced-modules-are-cohomologically-trivial.md), for the
  acyclicity of the $H$-modules $X^n(G, A)$, which makes $0 \to A \to X^\bullet(G, A)$ an acyclic resolution of the
  $H$-module $A$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §6, the induced module
  $\operatorname{Ind}_G^H(A)$ and the projection $\pi$, pp. 61–62, and Proposition (1.6.4) (Shapiro's lemma) with
  its proof, pp. 62–63.
