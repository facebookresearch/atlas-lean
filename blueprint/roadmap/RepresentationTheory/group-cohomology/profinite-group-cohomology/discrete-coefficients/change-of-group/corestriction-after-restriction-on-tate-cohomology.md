# Corestriction after restriction on Tate cohomology

Let $k$ be a commutative ring, $G$ a finite group, $H$ a subgroup and $A$ a $k$-linear representation of $G$. Then
for every $n \in \mathbb{Z}$, with the
[restriction and corestriction on Tate cohomology](restriction-and-corestriction-on-tate-cohomology.md),

$$
\operatorname{cor}^H_G \circ \operatorname{res}^G_H = (G : H) \cdot \mathrm{id} \colon \hat H^n(G, A) \longrightarrow
\hat H^n(G, A).
$$

Consequently, if $\hat H^n(H, \operatorname{Res}_H A) = 0$, then $(G : H)\, \hat H^n(G, A) = 0$. Since the
[Tate cohomology](../../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md) of the trivial group vanishes
in every degree, $\hat H^n(G, A)$ is annihilated by the order of $G$ for every $n \in \mathbb{Z}$.

## Depends on

- [Restriction and corestriction on Tate cohomology](restriction-and-corestriction-on-tate-cohomology.md), for
  $\operatorname{res}$ and $\operatorname{cor}$
- [Tate cohomology groups of a finite group](../../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md),
  for $\hat H^n$

## Proof depends on

- [The coinduction unit followed by the norm is multiplication by the index](unit-followed-by-norm-is-the-index.md),
  for $\nu_A \circ \iota_A = (G : H)$: the composite $\hat H^n(\nu_A) \circ \mathrm{sh}^{-1} \circ \mathrm{sh} \circ
  \hat H^n(\iota_A)$ is $\hat H^n(\nu_A \circ \iota_A)$, which is multiplication by $(G : H)$ since `tateCohomology`
  is additive in the morphism

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020), <https://www.jmilne.org/math/CourseNotes/CFT.pdf>:
  Chapter II, §3, p. 79 (the composite is still multiplication by $(G : H)$, and as $\hat H^r(\{1\}, M) = 0$ for all
  $r$, $\hat H^r(G, M)$ is killed by $|G|$ for all $r$).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §6, Proposition (1.6.1), finite case,
  p. 60.
