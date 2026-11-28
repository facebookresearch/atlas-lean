# Shapiro's lemma for Tate cohomology

Let $k$ be a commutative ring, $G$ a finite group, $H$ a subgroup and $A$ a $k$-linear representation of $H$. Then for
every $n \in \mathbb{Z}$ there is an isomorphism of
[Tate cohomology](../../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md) groups

$$
\mathrm{sh} \colon \hat H^n(G, \operatorname{Coind}_H^G A) \xrightarrow{\ \sim\ } \hat H^n(H, A),
$$

natural in $A$ and compatible with the connecting homomorphisms of short exact sequences of representations of $H$
(Mathlib's `TateCohomology.δ`), which for $n \ge 1$ corresponds, under the identifications
`TateCohomology.isoGroupCohomology` of $\hat H^n$ with $H^n$ for $G$ and for $H$, to Shapiro's isomorphism
`groupCohomology.coindIso A n` of group cohomology. Here $\operatorname{Coind}_H^G A$ is Mathlib's
`Rep.coind H.subtype A`, isomorphic to the induced representation `Rep.ind H.subtype A` since $H$ has finite index
(`Rep.indCoindIso`).

## Depends on

- [Tate cohomology groups of a finite group](../../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md),
  for $\hat H^n$

## Proof depends on

- [Tate cohomology groups of a finite group](../../../tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md),
  for the complete resolution computing $\hat H^n$, to which the comparison of cochains in the proof of Shapiro's
  lemma applies degreewise in all degrees

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §6, the Remark after Proposition
  (1.6.4), p. 63 ("If $G$ is finite, the same argument yields isomorphisms $\hat H^n(G, \operatorname{Ind}_G^H(A))
  \cong \hat H^n(H, A)$ for all $n \in \mathbb{Z}$").
- J. S. Milne, *Class Field Theory*, version 4.03 (2020), <https://www.jmilne.org/math/CourseNotes/CFT.pdf>:
  Chapter II, §3, p. 79 (Shapiro's lemma extends to all the Tate cohomology groups).
