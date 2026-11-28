# Ranks of ℓ-adic cohomology

Let $G$ be a profinite group and $\ell$ a prime number, and assume that the cohomology groups of $G$ with
coefficients in finite $\ell$-primary discrete modules are finite. Let $T$ be a topological $G$-module which is a
finitely generated, torsion-free $\mathbb{Z}_\ell$-module with its natural topology, on which $G$ acts
$\mathbb{Z}_\ell$-linearly, and let $V = T \otimes_{\mathbb{Z}_\ell} \mathbb{Q}_\ell$. Then for all $n$, for
[continuous cohomology](continuous-cohomology.md),

$$
\operatorname{rank}_{\mathbb{Z}_\ell} H^n_{\mathrm{cts}}(G, T) = \dim_{\mathbb{Q}_\ell} H^n_{\mathrm{cts}}(G, V)
= \operatorname{corank}_{\mathbb{Z}_\ell} H^n(G, T \otimes \mathbb{Q}_\ell/\mathbb{Z}_\ell),
$$

where the corank of an $\ell$-primary torsion group $X$ is the $\mathbb{Z}_\ell$-rank of its Pontryagin dual
$\operatorname{Hom}(X, \mathbb{Q}_\ell/\mathbb{Z}_\ell)$. Neukirch–Schmidt–Wingberg also identify these with the
$\mathbb{Z}_\ell$-rank of the homology $H_n(G, \operatorname{Hom}(T, \mathbb{Z}_\ell))$, which is not part of this page.

## Depends on

- [Continuous cohomology](continuous-cohomology.md), for $H^n_{\mathrm{cts}}(G, -)$
- [The ring of p-adic integers](../../../../NumberTheory/p-adic-numbers/p-adic-integers.md), for $\mathbb{Z}_\ell$
- [The field of p-adic numbers](../../../../NumberTheory/p-adic-numbers/p-adic-numbers.md), for $\mathbb{Q}_\ell$

## Proof depends on

- [Rational ℓ-adic cohomology](rational-l-adic-cohomology.md), for the first equality
- [Finite generation of ℓ-adic cohomology](finite-generation-of-l-adic-cohomology.md), for the finite generation
  and the isogeny that give the second

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter II, §7, Corollary (2.7.12), its first
  two equalities and their proof, p. 145.
