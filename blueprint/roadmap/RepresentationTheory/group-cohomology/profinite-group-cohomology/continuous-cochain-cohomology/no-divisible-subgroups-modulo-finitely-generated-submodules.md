# No divisible subgroups modulo finitely generated submodules

Let $G$ be a profinite group, $\ell$ a prime number and $T$ a topological $G$-module which, as a topological group,
is a finitely generated $\mathbb{Z}_\ell$-module with its natural ($\ell$-adic) topology, on which $G$ acts
$\mathbb{Z}_\ell$-linearly. Let $n \ge 0$ and let $Y$ be a finitely generated $\mathbb{Z}_\ell$-submodule of the
[continuous cohomology](continuous-cohomology.md) group $H^n_{\mathrm{cts}}(G, T)$. Then the quotient

$$
H^n_{\mathrm{cts}}(G, T) / Y
$$

contains no nontrivial $\ell$-divisible subgroup.

## Depends on

- [Continuous cohomology](continuous-cohomology.md), for $H^n_{\mathrm{cts}}(G, T)$ as a $\mathbb{Z}_\ell$-module
- [The ring of p-adic integers](../../../../NumberTheory/p-adic-numbers/p-adic-integers.md), for $\mathbb{Z}_\ell$
  and its topology

## Proof depends on

- [Continuous cohomology](continuous-cohomology.md), for the cochain complex
  $C^\bullet_{\mathrm{cts}}(G, T) = \varprojlim_i C^\bullet(G, T/\ell^i T)$, which justifies the infinite sums of
  cochains in the proof

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter II, §7, the setting before
  Proposition (2.7.8), and Proposition (2.7.8) with its proof (after Tate), p. 143.
