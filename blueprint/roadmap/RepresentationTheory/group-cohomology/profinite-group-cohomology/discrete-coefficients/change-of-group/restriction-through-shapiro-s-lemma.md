# Restriction through Shapiro's lemma

Let $k$ be a commutative ring, $G$ a group, $H$ a subgroup and $A$ a $k$-linear representation of $G$, with
restriction $\operatorname{Res}_H A$ to $H$. Let $\iota_A \colon A \to \operatorname{Coind}_H^G(\operatorname{Res}_H A)$
be the unit at $A$ of the adjunction $\operatorname{Res}_H \dashv \operatorname{Coind}_H^G$ (Mathlib's
`Rep.resCoindAdjunction k H.subtype`), the $G$-map $a \mapsto (g \mapsto g a)$. Then for every $n \ge 0$ the
restriction

$$
\operatorname{res}^G_H \colon H^n(G, A) \longrightarrow H^n(H, \operatorname{Res}_H A),
$$

the map `groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n` induced by the inclusion $H \to G$ and the identity
of $A$, is the composite of the map $H^n(G, A) \to H^n(G, \operatorname{Coind}_H^G(\operatorname{Res}_H A))$ induced
by $\iota_A$ (`groupCohomology.map (MonoidHom.id G) ι_A n`) with Shapiro's isomorphism
$H^n(G, \operatorname{Coind}_H^G(\operatorname{Res}_H A)) \cong H^n(H, \operatorname{Res}_H A)$
(`groupCohomology.coindIso (Rep.res H.subtype A) n`).

This is the restriction square of Neukirch–Schmidt–Wingberg, Proposition (1.6.5), for abstract groups; the
corresponding square for corestriction is the definition of
[corestriction for subgroups of finite index](corestriction-for-subgroups-of-finite-index.md).

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §6, the map $i$ before Proposition
  (1.6.5), p. 63, and Proposition (1.6.5), the right-hand diagram, pp. 63–64 ("For the restriction this is obvious").
- J. S. Milne, *Class Field Theory*, version 4.03 (2020), <https://www.jmilne.org/math/CourseNotes/CFT.pdf>:
  Chapter II, proof of Proposition 1.30, p. 70, which computes $\operatorname{Res}$ followed by Shapiro's isomorphism
  as the map induced by $m \mapsto (g \mapsto g m)$.
