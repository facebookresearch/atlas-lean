# Conjugation commutes with inflation, restriction and corestriction

Let $G$ be a profinite group, $A$ a discrete $G$-module and $\sigma \in G$. On
[cohomology](../cohomology-with-discrete-coefficients.md), for every $n \ge 0$, the conjugation $\sigma_*$ commutes
with inflation, restriction and corestriction:

1. for closed subgroups $H \subseteq K$ of $G$,
   $\sigma_* \circ \operatorname{res}^K_H = \operatorname{res}^{\sigma K}_{\sigma H} \circ \sigma_*
   \colon H^n(K, A) \to H^n(\sigma H \sigma^{-1}, A)$, where $\sigma K = \sigma K \sigma^{-1}$;
2. for a closed subgroup $K$, a closed subgroup $H \subseteq K$ normal in $K$ and
   $\inf^{K/H}_K \colon H^n(K/H, A^H) \to H^n(K, A)$,
   $\sigma_* \circ \inf^{K/H}_K = \inf^{\sigma K/\sigma H}_{\sigma K} \circ \sigma_*$, where
   $\sigma_* \colon H^n(K/H, A^H) \to H^n(\sigma K/\sigma H, A^{\sigma H})$ on the right is induced by the compatible
   pair $\sigma K/\sigma H \to K/H$, $\tau\,\sigma H \mapsto \sigma^{-1}\tau\sigma H$, and $A^H \to A^{\sigma H}$,
   $a \mapsto \sigma a$;
3. for an open subgroup $H \subseteq K$ of a closed subgroup $K$,
   $\sigma_* \circ \operatorname{cor}^H_K = \operatorname{cor}^{\sigma H}_{\sigma K} \circ \sigma_*$.

## Depends on

- [Inflation, restriction and conjugation](inflation-restriction-and-conjugation.md), for $\sigma_*$, $\inf$ and
  $\operatorname{res}$
- [Corestriction for open subgroups](corestriction.md), for $\operatorname{cor}$

## Proof depends on

- [Cohomology commutes with direct limits](../cohomology-commutes-with-direct-limits.md), for the compatibility of
  the maps induced by compatible pairs with composition, which gives 1 and 2 on the level of cochains
- [The cochain formula for corestriction](cochain-formula-for-corestriction.md), for the cochain-level computation
  in 3

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §5, Proposition (1.5.4), p. 50, and
  the remark after Proposition (1.5.5) that all this can be seen on the level of cochains, p. 51.
