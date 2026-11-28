# Cohomological dimension of a profinite group

Let $G$ be a profinite group, and let $\mathrm{Mod}(G)$ be the category of discrete $G$-modules and
$\mathrm{Mod}_t(G)$ the full subcategory of those that are torsion as abelian groups. The cohomological dimension
$\operatorname{cd} G$ (respectively the strict cohomological dimension $\operatorname{scd} G$) is the smallest integer
$n \ge 0$ such that

$$
H^q(G, A) = 0 \quad \text{for all } q > n
$$

and all $A \in \mathrm{Mod}_t(G)$ (respectively all $A \in \mathrm{Mod}(G)$), and is $\infty$ if no such integer
exists; here $H^q$ is the [cohomology](discrete-coefficients/cohomology-with-discrete-coefficients.md) of $G$. For a
prime number $p$, the cohomological $p$-dimension $\operatorname{cd}_p G$ (respectively the strict cohomological
$p$-dimension $\operatorname{scd}_p G$) is the smallest integer $n \ge 0$ such that the $p$-primary part
$H^q(G, A)(p)$, the elements of $p$-power order, vanishes for all $q > n$ and all $A \in \mathrm{Mod}_t(G)$
(respectively all $A \in \mathrm{Mod}(G)$), and is $\infty$ if no such integer exists. Then

$$
\operatorname{cd} G = \sup_p \operatorname{cd}_p G \qquad \text{and} \qquad \operatorname{scd} G = \sup_p \operatorname{scd}_p G.
$$

For a field $k$ with separable closure $\bar k$, $\operatorname{cd}_p(k)$ and $\operatorname{cd}(k)$ denote those of
its absolute Galois group $G_k = G(\bar k | k)$.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](discrete-coefficients/cohomology-with-discrete-coefficients.md),
  for $H^q(G, A)$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter III, §3, Definition (3.3.1) and the
  remark after it, p. 172; Chapter VI, §5, the notation before Proposition (6.5.10), p. 365.
