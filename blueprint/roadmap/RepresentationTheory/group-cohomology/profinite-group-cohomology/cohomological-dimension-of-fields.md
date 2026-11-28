# Cohomological dimension of a field and the multiplicative group

Let $k$ be a field, $p$ a prime number different from the characteristic of $k$, and $n$ a natural number. For an
algebraic extension $K | k$ inside a separable closure $\bar k$ of $k$, write $H^i(K, -)$ for the
[cohomology](discrete-coefficients/cohomology-with-discrete-coefficients.md) of the absolute Galois group
$G_K = G(\bar k | K)$ and $\bar k^\times$ for the multiplicative group of $\bar k$. The following conditions are
equivalent:

1. $\operatorname{cd}_p(k) \le n$, for the [cohomological $p$-dimension](cohomological-dimension.md) of $G_k$;
2. $H^{n+1}(K, \bar k^\times)(p) = 0$ and $H^n(K, \bar k^\times)$ is $p$-divisible, for every algebraic extension
   $K | k$;
3. $H^{n+1}(K, \bar k^\times)(p) = 0$ and $H^n(K, \bar k^\times)$ is $p$-divisible, for every finite separable
   extension $K | k$.

## Depends on

- [Cohomological dimension of a profinite group](cohomological-dimension.md), for $\operatorname{cd}_p(k)$
- [Cohomology of a profinite group with discrete coefficients](discrete-coefficients/cohomology-with-discrete-coefficients.md),
  for $H^i(K, \bar k^\times)$

## Proof depends on

- [The long exact cohomology sequence](discrete-coefficients/long-exact-cohomology-sequence.md), for the Kummer
  sequence $1 \to \mu_p \to \bar k^\times \xrightarrow{p} \bar k^\times \to 1$, which turns the condition on $K$ into
  $H^{n+1}(K, \mu_p) = 0$
- [Properties of cohomological dimension](properties-of-cohomological-dimension.md), for the closed subgroups
  $G_K$ ((3.3.5)), the $p$-Sylow subgroups ((3.3.6)) and the criterion (3.3.2)(iii)
- [Cohomology commutes with direct limits](discrete-coefficients/cohomology-commutes-with-direct-limits.md), for
  writing the fixed field of a $p$-Sylow subgroup as a union of finite separable extensions containing $\mu_p$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter VI, §5, Proposition (6.5.11) and its
  proof, p. 365.
