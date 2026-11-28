# The coinduction unit followed by the norm is multiplication by the index

Let $k$ be a commutative ring, $G$ a group, $H$ a subgroup of finite index $(G : H)$ and $A$ a $k$-linear
representation of $G$. Let $\iota_A \colon A \to \operatorname{Coind}_H^G(\operatorname{Res}_H A)$ be the unit at $A$
of the adjunction $\operatorname{Res}_H \dashv \operatorname{Coind}_H^G$ (`Rep.resCoindAdjunction k H.subtype`), as in
[Restriction through Shapiro's lemma](restriction-through-shapiro-s-lemma.md), and
$\nu_A \colon \operatorname{Coind}_H^G(\operatorname{Res}_H A) \to A$ the counit at $A$ of the adjunction
$\operatorname{Coind}_H^G \dashv \operatorname{Res}_H$ (`Rep.coindResAdjunction k H`), as in
[Corestriction for subgroups of finite index](corestriction-for-subgroups-of-finite-index.md). Then

$$
\nu_A \circ \iota_A = (G : H) \cdot \mathrm{id}_A
$$

as morphisms of representations $A \to A$: for $a \in A$, $\iota_A(a)$ is $g \mapsto g a$, and
$\nu_A(\iota_A(a)) = \sum_{\sigma \in G/H} \sigma \sigma^{-1} a = (G : H)\, a$.

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020), <https://www.jmilne.org/math/CourseNotes/CFT.pdf>:
  Chapter II, proof of Proposition 1.30, p. 70 (the composite $M \to \operatorname{Ind}_H^G(M) \to M$,
  $m \mapsto \varphi_m \mapsto \sum_s s\varphi_m(s^{-1})$, is multiplication by $(G : H)$).
