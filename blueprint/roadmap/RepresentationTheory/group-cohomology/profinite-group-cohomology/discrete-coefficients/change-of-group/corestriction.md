# Corestriction for open subgroups

Let $G$ be a profinite group, $U$ an open subgroup and $A$ a discrete $G$-module. The induced module
$\operatorname{Ind}_G^U(A)$ of [Shapiro's lemma](../shapiro-s-lemma.md), the continuous maps $x \colon G \to A$ with
$x(\tau\sigma) = \tau x(\sigma)$ for $\tau \in U$, carries the $G$-homomorphism

$$
\nu \colon \operatorname{Ind}_G^U(A) \longrightarrow A, \qquad \nu(x) = \sum_{\sigma \in G/U} \sigma\, x(\sigma^{-1}),
$$

where $\sigma$ runs through a system of representatives of the left cosets $G/U$ (the sum does not depend on the
choice). For $n \ge 0$ the corestriction

$$
\operatorname{cor}^U_G \colon H^n(U, A) \longrightarrow H^n(G, A)
$$

of [cohomology](../cohomology-with-discrete-coefficients.md) groups is the composite of the inverse of Shapiro's
isomorphism $\mathrm{sh} \colon H^n(G, \operatorname{Ind}_G^U(A)) \xrightarrow{\sim} H^n(U, A)$ with the map
$\nu_* \colon H^n(G, \operatorname{Ind}_G^U(A)) \to H^n(G, A)$. It is natural in $A$. By
[the cochain formula for corestriction](cochain-formula-for-corestriction.md) it is the corestriction that
Neukirch–Schmidt–Wingberg define from the norm on the standard resolution, which in degree $0$ is the norm
$N_{G/U} \colon A^U \to A^G$.

For abstract groups and a subgroup of finite index, the same construction is
[Corestriction for subgroups of finite index](corestriction-for-subgroups-of-finite-index.md).

## Depends on

- [Shapiro's lemma for profinite groups](../shapiro-s-lemma.md), for $\operatorname{Ind}_G^U(A)$ and $\mathrm{sh}$
- [Cohomology of a profinite group with discrete coefficients](../cohomology-with-discrete-coefficients.md), for
  the cohomology groups and the map $\nu_*$ that a homomorphism of modules induces

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §6, the homomorphism $\nu$ before
  Proposition (1.6.5) and the left-hand diagram of Proposition (1.6.5), p. 63; Chapter I, §5, 4. Corestriction,
  p. 47.
- J. S. Milne, *Class Field Theory*, version 4.03 (2020), <https://www.jmilne.org/math/CourseNotes/CFT.pdf>:
  Chapter II, Example 1.29, p. 70 (corestriction as the map induced by $\varphi \mapsto \sum_s s\varphi(s^{-1})$
  composed with Shapiro's isomorphism).
