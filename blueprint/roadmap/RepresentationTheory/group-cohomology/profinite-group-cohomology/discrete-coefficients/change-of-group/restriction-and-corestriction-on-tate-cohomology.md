# Restriction and corestriction on Tate cohomology

Let $k$ be a commutative ring, $G$ a finite group, $H$ a subgroup and $A$ a $k$-linear representation of $G$, with
restriction $\operatorname{Res}_H A$ to $H$. Let $\iota_A \colon A \to \operatorname{Coind}_H^G(\operatorname{Res}_H A)$
and $\nu_A \colon \operatorname{Coind}_H^G(\operatorname{Res}_H A) \to A$ be the unit and the counit of
[Restriction through Shapiro's lemma](restriction-through-shapiro-s-lemma.md) and
[Corestriction for subgroups of finite index](corestriction-for-subgroups-of-finite-index.md), and $\mathrm{sh}$
the isomorphism of [Shapiro's lemma for Tate cohomology](shapiro-s-lemma-for-tate-cohomology.md). For every
$n \in \mathbb{Z}$ the restriction and the corestriction on
[Tate cohomology](../../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md) are

$$
\operatorname{res}^G_H = \mathrm{sh} \circ \hat H^n(\iota_A) \colon \hat H^n(G, A) \to \hat H^n(H, \operatorname{Res}_H A),
\qquad
\operatorname{cor}^H_G = \hat H^n(\nu_A) \circ \mathrm{sh}^{-1} \colon \hat H^n(H, \operatorname{Res}_H A) \to
\hat H^n(G, A),
$$

where $\hat H^n(f)$ is the map Mathlib's `tateCohomology` gives a morphism $f$ of representations of $G$. They are
$k$-linear and natural in $A$.

## Depends on

- [Shapiro's lemma for Tate cohomology](shapiro-s-lemma-for-tate-cohomology.md), for $\mathrm{sh}$
- [Tate cohomology groups of a finite group](../../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md),
  for $\hat H^n$ and its functoriality

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020), <https://www.jmilne.org/math/CourseNotes/CFT.pdf>:
  Chapter II, §3, p. 79 (the restriction and corestriction maps of (1.27) and (1.29) extend to all the Tate cohomology
  groups), with Example 1.29, p. 70, for the construction of corestriction through Shapiro's lemma.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §6, the maps $i$ and $\nu$ before
  Proposition (1.6.5) and Proposition (1.6.5), pp. 63–64, and the Remark after Proposition (1.6.4), p. 63.
