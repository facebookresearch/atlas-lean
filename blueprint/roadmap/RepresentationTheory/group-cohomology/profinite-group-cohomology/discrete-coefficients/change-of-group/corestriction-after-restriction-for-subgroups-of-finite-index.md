# Corestriction after restriction for subgroups of finite index

Let $k$ be a commutative ring, $G$ a group, $H$ a subgroup of finite index $(G : H)$ and $A$ a $k$-linear
representation of $G$. Then for every $n \ge 0$ the
[corestriction](corestriction-for-subgroups-of-finite-index.md) after the restriction
(`groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n`) is multiplication by the index:

$$
\operatorname{cor}^H_G \circ \operatorname{res}^G_H = (G : H) \cdot \mathrm{id} \colon H^n(G, A) \longrightarrow H^n(G, A).
$$

In particular, if $G$ is finite of order $m$, then $m\, H^n(G, A) = 0$ for every $n \ge 1$, since $H^n$ of the trivial
group vanishes in positive degrees.

## Depends on

- [Corestriction for subgroups of finite index](corestriction-for-subgroups-of-finite-index.md), for
  $\operatorname{cor}^H_G$

## Proof depends on

- [Restriction through Shapiro's lemma](restriction-through-shapiro-s-lemma.md), for
  $\operatorname{res}^G_H$ as the map induced by the unit $\iota_A$ followed by Shapiro's isomorphism, so that
  $\operatorname{cor} \circ \operatorname{res}$ is the map induced by $\nu_A \circ \iota_A$ (`groupCohomology.map_comp`)
- [The coinduction unit followed by the norm is multiplication by the index](unit-followed-by-norm-is-the-index.md),
  for $\nu_A \circ \iota_A = (G : H)$, which induces multiplication by $(G : H)$ on cohomology since the induced maps are
  additive in the morphism

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020), <https://www.jmilne.org/math/CourseNotes/CFT.pdf>:
  Chapter II, Proposition 1.30 with its proof and Corollary 1.31, p. 70.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §5, Corollary (1.5.7), first formula,
  p. 51.
