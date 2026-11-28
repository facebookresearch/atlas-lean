# Continuous cohomology of a countable inverse limit of finite modules

This node is still to be broken down. Let $G$ be a profinite group and $A$ a compact $G$-module with a presentation
$A = \varprojlim_{n \in \mathbb{N}} A_n$ as a countable inverse limit of finite discrete $G$-modules. Then for every
$i \ge 1$ there is a natural exact sequence

$$
0 \longrightarrow \varprojlim\nolimits^1_n H^{i-1}(G, A_n) \longrightarrow H^i_{\mathrm{cts}}(G, A)
\longrightarrow \varprojlim_n H^i(G, A_n) \longrightarrow 0
$$

of [continuous cohomology](continuous-cohomology.md) groups, with $H^j(G, A_n) = H^j_{\mathrm{cts}}(G, A_n)$ for the
discrete modules $A_n$ and $\varprojlim^1$ the [first derived limit](first-derived-limit-of-a-tower.md).

## Expansion

This node is still to be broken down. A good expansion states and links:

- the reduction to a presentation with surjective transition maps (the beginning of the proof of (2.7.5));
- the identification of $C^\bullet_{\mathrm{cts}}(G, A)$ with $\varprojlim_n C^\bullet(G, A_n)$, whose transition maps
  are surjective;
- the exact sequence for the cohomology of an inverse limit of a tower of cochain complexes with surjective
  transition maps, which Neukirch–Schmidt–Wingberg obtain from the spectral sequence of a composite of derived
  functors ((2.6.6)) and Proposition (2.7.4), with Jannsen's description of the injective inverse systems.

## Depends on

- [Continuous cohomology](continuous-cohomology.md), for $H^i_{\mathrm{cts}}(G, -)$
- [The first derived limit of a tower](first-derived-limit-of-a-tower.md), for $\varprojlim^1$

## Proof depends on

- [The first derived limit of a tower](first-derived-limit-of-a-tower.md), for $\varprojlim^1$ as a cokernel and
  the vanishing of $\varprojlim^p$ for $p \ge 2$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter II, §7, Theorem (2.7.5) and its
  proof, pp. 141–142, with the preparations on inverse systems, pp. 138–139.
