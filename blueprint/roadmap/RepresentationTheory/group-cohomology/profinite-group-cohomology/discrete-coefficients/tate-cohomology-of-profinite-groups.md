# Tate cohomology of profinite groups

This node is still to be broken down. Let $G$ be a profinite group and $A$ a discrete $G$-module. The Tate cohomology
groups of $G$ are $\hat H^i(G, A) = H^i(G, A)$ for $i > 0$ ([cohomology](cohomology-with-discrete-coefficients.md))
and, for $i \le 0$,

$$
\hat H^i(G, A) = \varprojlim_{U,\ \mathrm{def}} \hat H^i(G/U, A^U),
$$

the inverse limit, over the open normal subgroups $U$ of $G$, of the
[Tate cohomology](../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md) of the finite groups $G/U$
along the deflation maps. For $i = 0$ the finite levels are $\hat H^0(G/U, A^U) = A^G / N_{G/U}A^U$, and
$A^G / N_G A$ injects into $\hat H^0(G, A)$, where $N_G A = \bigcap_U N_{G/U} A^U$ is the group of universal norms.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the deflation maps $\mathrm{def} \colon \hat H^i(G/V, A^V) \to \hat H^i(G/U, A^U)$ for $V \subseteq U$, defined on
  the complete standard resolution (Neukirch–Schmidt–Wingberg, Lemma (1.9.4) and Propositions (1.9.5),
  (1.9.6)), and Definition (1.9.3);
- the cup products of Corollary (1.9.7);
- Lemma (1.9.8): for $A$ finitely generated over $\mathbb{Z}$ and $p$ with $p^\infty \mid \#G$,
  $\hat H^0(G, A)(p) \cong A^G \otimes \mathbb{Z}_p$, and the long exact sequences of Proposition (1.9.9);
- Lemma (1.9.11): for a [level-compact module](level-compact-modules.md),
  $\hat H^0(G, A) = A^G / N_G A$ and $\hat H^{-1}(G, A) = N_G A / I_G A$, and the profinite topology on
  $\hat H^i(G, A)$ for $i \le 0$; and Lemma (1.9.12).

## Depends on

- [Cohomology of a profinite group with discrete coefficients](cohomology-with-discrete-coefficients.md), for
  $H^i(G, A)$, $i > 0$
- [Tate cohomology groups of a finite group](../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md),
  for the finite levels

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §9, Definition (1.9.3), p. 86;
  Lemma (1.9.4) to Corollary (1.9.7), pp. 86–89; Lemma (1.9.8) and Proposition (1.9.9), p. 90; the universal
  norms and Lemma (1.9.11), pp. 90–91.
