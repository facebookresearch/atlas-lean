# The double coset formula

Let $G$ be a profinite group, $U$ and $V$ closed subgroups with $V$ open, and $A$ a discrete $G$-module. Let $\sigma$
run through a system of representatives of the finite double coset decomposition $G = \bigcup_\sigma U \sigma V$
(disjoint). Then for every $n \ge 0$, on [cohomology](../cohomology-with-discrete-coefficients.md),

$$
\operatorname{res}^G_U \circ \operatorname{cor}^V_G = \sum_\sigma
\operatorname{cor}^{U \cap \sigma V \sigma^{-1}}_U \circ \sigma_* \circ
\operatorname{res}^V_{V \cap \sigma^{-1} U \sigma} \colon H^n(V, A) \longrightarrow H^n(U, A),
$$

where $\sigma_* \colon H^n(V \cap \sigma^{-1}U\sigma, A) \to H^n(U \cap \sigma V \sigma^{-1}, A)$ is the conjugation,
$U \cap \sigma V \sigma^{-1}$ being open in $U$. In degree $0$ it is the identity
$N_{G/V} a = \sum_\sigma N_{U/U \cap \sigma V\sigma^{-1}}(\sigma a)$ for $a \in A^V$.

## Depends on

- [Inflation, restriction and conjugation](inflation-restriction-and-conjugation.md), for $\operatorname{res}$ and
  $\sigma_*$
- [Corestriction for open subgroups](corestriction.md), for $\operatorname{cor}$

## Proof depends on

- [Cohomology as a direct limit over finite quotients](../cohomology-as-a-direct-limit-over-finite-quotients.md),
  [Conjugation commutes with inflation, restriction and corestriction](conjugation-commutes-with-inflation-restriction-and-corestriction.md)
  and [Inflation commutes with restriction and corestriction](inflation-commutes-with-restriction-and-corestriction.md),
  for the reduction to a finite group $G$
- [Functoriality and the connecting homomorphisms](functoriality-and-connecting-homomorphisms.md),
  [the long exact cohomology sequence](../long-exact-cohomology-sequence.md) and
  [Induced modules are acyclic](../induced-modules-are-acyclic.md), for the dimension shifting to degree $0$
- [The cochain formula for corestriction](cochain-formula-for-corestriction.md), for $\operatorname{cor}$ in degree
  $0$ as the norm

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §5, Proposition (1.5.6) with its
  proof, p. 51.
