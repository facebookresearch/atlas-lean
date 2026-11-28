# Rational ℓ-adic cohomology

Let $G$ be a profinite group, $\ell$ a prime number and $T$ a topological $G$-module which is a finitely generated,
torsion-free $\mathbb{Z}_\ell$-module with its natural topology, on which $G$ acts $\mathbb{Z}_\ell$-linearly.
Tensoring $T$ over $\mathbb{Z}_\ell$ with $0 \to \mathbb{Z}_\ell \to \mathbb{Q}_\ell \to \mathbb{Q}_\ell/\mathbb{Z}_\ell \to 0$
gives an exact sequence

$$
0 \longrightarrow T \longrightarrow V \longrightarrow W \longrightarrow 0,
$$

in which $V = T \otimes \mathbb{Q}_\ell$ is a finite-dimensional $\mathbb{Q}_\ell$-vector space, $T$ an open compact
subgroup and $W = T \otimes \mathbb{Q}_\ell/\mathbb{Z}_\ell$ a discrete divisible $\ell$-primary torsion group. Then
for all $n$, for [continuous cohomology](continuous-cohomology.md),

$$
H^n_{\mathrm{cts}}(G, V) \cong H^n_{\mathrm{cts}}(G, T) \otimes_{\mathbb{Z}_\ell} \mathbb{Q}_\ell,
$$

and in the long exact sequence of $0 \to T \to V \to W \to 0$ the kernel of the connecting homomorphism
$\delta \colon H^{n-1}(G, W) \to H^n_{\mathrm{cts}}(G, T)$ is the maximal divisible subgroup of $H^{n-1}(G, W)$, and
its image is the torsion subgroup of $H^n_{\mathrm{cts}}(G, T)$.

## Depends on

- [Continuous cohomology](continuous-cohomology.md), for $H^n_{\mathrm{cts}}(G, -)$
- [The long exact sequence of continuous cohomology](long-exact-sequence-for-continuous-cohomology.md), for the
  connecting homomorphism $\delta$ of $0 \to T \to V \to W \to 0$
- [The ring of p-adic integers](../../../../NumberTheory/p-adic-numbers/p-adic-integers.md), for $\mathbb{Z}_\ell$
- [The field of p-adic numbers](../../../../NumberTheory/p-adic-numbers/p-adic-numbers.md), for $\mathbb{Q}_\ell$

## Proof depends on

- [The long exact sequence of continuous cohomology](long-exact-sequence-for-continuous-cohomology.md), for the
  long exact sequence, tensored with $\mathbb{Q}_\ell$
- [No divisible subgroups modulo finitely generated submodules](no-divisible-subgroups-modulo-finitely-generated-submodules.md),
  for the divisible subgroups of $H^{n-1}(G, W)$ lying in the kernel of $\delta$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter II, §7, the sequence $(\ast)$ and
  Proposition (2.7.11) with its proof, pp. 144–145.
