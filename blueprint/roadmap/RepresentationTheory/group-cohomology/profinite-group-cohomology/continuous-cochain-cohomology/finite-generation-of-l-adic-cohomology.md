# Finite generation of ℓ-adic cohomology

Let $G$ be a profinite group and $\ell$ a prime number, and assume that the cohomology groups $H^n(G, M)$ of $G$
with coefficients in finite $\ell$-primary discrete modules $M$ are finite. Let $T$ be a topological $G$-module which
is a finitely generated $\mathbb{Z}_\ell$-module with its natural topology, on which $G$ acts
$\mathbb{Z}_\ell$-linearly. Then for all $n$ the [continuous cohomology](continuous-cohomology.md)
$H^n_{\mathrm{cts}}(G, T)$ is a finitely generated $\mathbb{Z}_\ell$-module, and the canonical map

$$
H^n_{\mathrm{cts}}(G, T) \otimes \mathbb{Q}_\ell/\mathbb{Z}_\ell \longrightarrow H^n(G, T \otimes \mathbb{Q}_\ell/\mathbb{Z}_\ell)
$$

is an isogeny, that is, it has finite kernel and finite cokernel; here $T \otimes \mathbb{Q}_\ell/\mathbb{Z}_\ell$,
over $\mathbb{Z}_\ell$, is a discrete $G$-module.

## Depends on

- [Continuous cohomology](continuous-cohomology.md), for $H^n_{\mathrm{cts}}(G, -)$, which for the discrete modules
  $M$ and $T \otimes \mathbb{Q}_\ell/\mathbb{Z}_\ell$ is their cohomology
- [The ring of p-adic integers](../../../../NumberTheory/p-adic-numbers/p-adic-integers.md), for $\mathbb{Z}_\ell$
- [The field of p-adic numbers](../../../../NumberTheory/p-adic-numbers/p-adic-numbers.md), for $\mathbb{Q}_\ell$

## Proof depends on

- [A finite generation criterion for ℓ-adic cohomology](finite-generation-criterion-for-l-adic-cohomology.md),
  for the finite generation and the finiteness of kernel and cokernel
- [The long exact sequence of continuous cohomology](long-exact-sequence-for-continuous-cohomology.md), for the
  exact sequences $0 \to H^n_{\mathrm{cts}}(G, T)/\ell^m \to H^n(G, T/\ell^m) \to {}_{\ell^m}H^{n+1}_{\mathrm{cts}}(G, T) \to 0$
  of $0 \to T \xrightarrow{\ell^m} T \to T/\ell^m \to 0$, after replacing $T$ by a torsion-free open submodule
- [Cohomology commutes with direct limits](../discrete-coefficients/cohomology-commutes-with-direct-limits.md),
  for $H^n(G, T \otimes \mathbb{Q}_\ell/\mathbb{Z}_\ell) = \varinjlim_m H^n(G, T/\ell^m)$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter II, §7, Corollary (2.7.10) and its
  proof, p. 144.
