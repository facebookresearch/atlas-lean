# Corestriction after restriction

Let $G$ be a profinite group, $U$ an open subgroup and $A$ a discrete $G$-module. Then for every $n \ge 0$ the
[corestriction](corestriction.md) after the [restriction](inflation-restriction-and-conjugation.md) is
multiplication by the index:

$$
\operatorname{cor}^U_G \circ \operatorname{res}^G_U = (G : U) \cdot \mathrm{id} \colon H^n(G, A) \longrightarrow
H^n(G, A).
$$

## Depends on

- [Inflation, restriction and conjugation](inflation-restriction-and-conjugation.md), for
  $\operatorname{res}^G_U$
- [Corestriction for open subgroups](corestriction.md), for $\operatorname{cor}^U_G$

## Proof depends on

- [Restriction through Shapiro's lemma for profinite groups](restriction-through-shapiro-s-lemma-for-profinite-groups.md),
  for $\operatorname{res} = \mathrm{sh} \circ i_*$, so that $\operatorname{cor} \circ \operatorname{res} =
  \nu_* \circ \mathrm{sh}^{-1} \circ \mathrm{sh} \circ i_* = (\nu \circ i)_*$, where
  $\nu(i(a)) = \sum_{\sigma \in G/U} \sigma \sigma^{-1} a = (G : U)\, a$, and $(G : U) \cdot \mathrm{id}_A$ induces
  multiplication by $(G : U)$ on cohomology

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §5, Corollary (1.5.7), first formula,
  p. 51.
- J. S. Milne, *Class Field Theory*, version 4.03 (2020), <https://www.jmilne.org/math/CourseNotes/CFT.pdf>:
  Chapter II, proof of Proposition 1.30, p. 70, for the argument through Shapiro's lemma.
