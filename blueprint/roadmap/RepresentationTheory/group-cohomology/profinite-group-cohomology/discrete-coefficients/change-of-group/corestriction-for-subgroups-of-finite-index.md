# Corestriction for subgroups of finite index

Let $k$ be a commutative ring, $G$ a group, $H$ a subgroup of finite index and $A$ a $k$-linear representation of
$G$, with restriction $\operatorname{Res}_H A$ to $H$. Let
$\nu_A \colon \operatorname{Coind}_H^G(\operatorname{Res}_H A) \to A$ be the counit at $A$ of the adjunction
$\operatorname{Coind}_H^G \dashv \operatorname{Res}_H$ for a subgroup of finite index (Mathlib's
`Rep.coindResAdjunction k H`), the $G$-map $x \mapsto \sum_{\sigma \in G/H} \sigma\, x(\sigma^{-1})$ over a system of
representatives of the left cosets. For $n \ge 0$ the corestriction

$$
\operatorname{cor}^H_G \colon H^n(H, \operatorname{Res}_H A) \longrightarrow H^n(G, A)
$$

is the composite of the inverse of Shapiro's isomorphism
$H^n(G, \operatorname{Coind}_H^G(\operatorname{Res}_H A)) \cong H^n(H, \operatorname{Res}_H A)$
(`groupCohomology.coindIso (Rep.res H.subtype A) n`) with the map
$H^n(G, \operatorname{Coind}_H^G(\operatorname{Res}_H A)) \to H^n(G, A)$ that $\nu_A$ induces on Mathlib's group
cohomology. It is $k$-linear and natural in $A$. In degree $0$, under $H^0(H, A) = A^H$ and $H^0(G, A) = A^G$, this
construction recovers the norm $N_{G/H} \colon A^H \to A^G$, $a \mapsto \sum_{\sigma \in G/H} \sigma a$, with which
Milne starts.

In degree $2$ the corestriction computed from a transversal by cocycles is
[Corestriction on second cohomology](../../../../not-yet-classified/corestriction/cores.md).

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020), <https://www.jmilne.org/math/CourseNotes/CFT.pdf>:
  Chapter II, Example 1.29, p. 70 (the norm $\mathrm{Nm}_{G/H}$ and its extension to $\mathrm{Cor}$ through Shapiro's
  lemma and the map $\varphi \mapsto \sum_s s\varphi(s^{-1})$).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §5, 4. Corestriction, p. 47 (for
  $n = 0$ the norm); Chapter I, §6, the map $\nu$ before Proposition (1.6.5) and the left-hand diagram of (1.6.5),
  p. 63.
