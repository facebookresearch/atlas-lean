# Inflation, restriction and conjugation

Let $G$ be a profinite group and $A$ a discrete $G$-module. The following are maps of
[cohomology](../cohomology-with-discrete-coefficients.md) groups induced by compatible pairs
$(\varphi \colon G' \to G,\ f \colon A \to A')$, $f(\varphi(\sigma')a) = \sigma' f(a)$, through
$C^n(G, A) \to C^n(G', A')$, $x \mapsto f \circ x \circ \varphi$, as in
[Cohomology commutes with direct limits](../cohomology-commutes-with-direct-limits.md); for every $n \ge 0$:

1. **Conjugation.** For a closed subgroup $H$, an $H$-submodule $B$ of $A$ and $\sigma \in G$, the pair
   ${}^{\sigma}H \to H$, $\tau \mapsto \sigma^{-1}\tau\sigma$, and $B \to \sigma B$, $b \mapsto \sigma b$, where
   ${}^{\sigma}H = \sigma H \sigma^{-1}$, induces
   $\sigma_* \colon H^n(H, B) \to H^n({}^{\sigma}H, \sigma B)$, an isomorphism with $1_* = \mathrm{id}$ and
   $(\sigma\tau)_* = \sigma_* \tau_*$.
2. **Inflation.** For a closed normal subgroup $H$, the projection $G \to G/H$ and the inclusion $A^H \to A$ induce
   $\inf^{G/H}_G \colon H^n(G/H, A^H) \to H^n(G, A)$.
3. **Restriction.** For a closed subgroup $H$, the inclusion $H \to G$ and $\mathrm{id}_A$ induce
   $\operatorname{res}^G_H \colon H^n(G, A) \to H^n(H, A)$.

For abstract groups and representations, Mathlib's `groupCohomology.map` is the map induced by a compatible pair, and
`groupCohomology.resNatTrans` and `groupCohomology.infNatTrans` are restriction and inflation, natural in the
representation.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](../cohomology-with-discrete-coefficients.md), for
  the cohomology groups
- [Cohomology commutes with direct limits](../cohomology-commutes-with-direct-limits.md), for the maps induced by
  compatible pairs and their compatibility with composition

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §5, the compatible pairs, p. 45, and
  1. Conjugation, 2. Inflation and 3. Restriction, pp. 46–47.
