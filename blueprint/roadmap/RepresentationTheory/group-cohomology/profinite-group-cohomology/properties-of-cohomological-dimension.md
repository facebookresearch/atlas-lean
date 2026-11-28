# Properties of cohomological dimension

This node is still to be broken down. It covers the basic properties of the
[cohomological dimension](cohomological-dimension.md) of a profinite group $G$ and a prime number $p$: that
$\operatorname{cd}_p G = \infty$ when $G$ has an element of order $p$; the criterion that $\operatorname{cd}_p G \le n$ if
and only if $H^{n+1}(G, A) = 0$ for all simple discrete $G$-modules $A$ with $pA = 0$, so that a pro-$p$-group has
$\operatorname{cd} G \le n$ if and only if $H^{n+1}(G, \mathbb{Z}/p\mathbb{Z}) = 0$; the inequalities
$\operatorname{cd}_p G \le \operatorname{scd}_p G \le \operatorname{cd}_p G + 1$; and the behaviour under closed, open,
Sylow and normal subgroups.

## Expansion

This node is still to be broken down. A good expansion states and links:

- Proposition (3.3.2): the equivalence of $\operatorname{cd}_p G \le n$, of $H^q(G, A) = 0$ for all $q > n$ and all
  $p$-torsion $A$, and of $H^{n+1}(G, A) = 0$ for all simple $A$ with $pA = 0$;
- Proposition (3.3.3), $\operatorname{cd}_p G \le \operatorname{scd}_p G \le \operatorname{cd}_p G + 1$, and Corollary
  (3.3.4): if $\operatorname{cd}_p G = n < \infty$, then $\operatorname{scd}_p G = n$ if and only if
  $H^{n+1}(U, \mathbb{Z})(p) = 0$ for all open subgroups $U$; and the example $\operatorname{cd}_p \hat{\mathbb{Z}} = 1$,
  $\operatorname{scd}_p \hat{\mathbb{Z}} = 2$;
- Proposition (3.3.5): $\operatorname{cd}_p H \le \operatorname{cd}_p G$ and $\operatorname{scd}_p H \le \operatorname{scd}_p G$
  for a closed subgroup $H$, with equality if $(G : H)$ is prime to $p$, or if $H$ is open and
  $\operatorname{cd}_p G < \infty$;
- Corollary (3.3.6): $\operatorname{cd}_p G = \operatorname{cd}_p G_p = \operatorname{cd} G_p$ and
  $\operatorname{scd}_p G = \operatorname{scd}_p G_p = \operatorname{scd} G_p$ for a $p$-Sylow subgroup $G_p$; and
  Corollary (3.3.7): $\operatorname{cd}_p G = 0$ if and only if $\#G$ is prime to $p$;
- Proposition (3.3.8): $\operatorname{cd}_p G \le \operatorname{cd}_p G/H + \operatorname{cd}_p H$ for a closed normal
  subgroup $H$, with equality under the finiteness hypotheses stated there.

## Depends on

- [Cohomological dimension of a profinite group](cohomological-dimension.md), for $\operatorname{cd}_p$ and
  $\operatorname{scd}_p$

## Proof depends on

- [Shapiro's lemma for profinite groups](discrete-coefficients/shapiro-s-lemma.md), for (3.3.5)
- [Inflation, restriction and corestriction for profinite groups](discrete-coefficients/inflation-restriction-and-corestriction.md),
  for the injectivity of restriction to subgroups of index prime to $p$
- [The Hochschild–Serre spectral sequence](discrete-coefficients/hochschild-serre-spectral-sequence.md), for (3.3.8)
- [The long exact cohomology sequence](discrete-coefficients/long-exact-cohomology-sequence.md), for the dimension
  shifting in (3.3.2) and (3.3.3)

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter III, §3, the remark after Definition
  (3.3.1), p. 172, Propositions (3.3.2)–(3.3.8) and the example after (3.3.4), pp. 172–175.
