# Restriction, corestriction, inflation and Tate's theorem in group cohomology

This node is still to be broken down. It covers the functorial maps of the cohomology of a finite group
that the cohomological proofs of class field theory use, Tate's theorem and the elementary computations
these proofs rely on, following Milne's Chapter II. Let $G$ be a finite group, $H$ a subgroup and $M$ a
$G$-module; $\hat H^r$ denotes Tate cohomology, which agrees with ordinary cohomology for $r \ge 1$. It
contains the following statements.

1. **Corestriction.** There are corestriction maps $\mathrm{Cor} \colon H^r(H, M) \to H^r(G, M)$, given
   on $H^0$ by $m \mapsto \sum_{s \in G/H} s m$, such that $\mathrm{Cor} \circ \mathrm{Res}$ is
   multiplication by the index $(G : H)$ (Milne, Proposition II.1.30). Consequently $|G|$ kills
   $H^r(G, M)$ for $r > 0$, these groups are finite when $M$ is finitely generated, and restriction to
   a Sylow $p$-subgroup is injective on the $p$-primary component of $H^r(G, M)$ (Milne, Corollaries
   II.1.31–1.33). Restriction and corestriction extend to Tate cohomology with the same properties, and
   Shapiro's lemma holds for it (Milne, Section II.3, before Proposition 3.2); on
   $\hat H^{-2}(\cdot, \mathbb{Z}) = (\cdot)^{\mathrm{ab}}$, corestriction from $H$ to $G$ is the map
   $H^{\mathrm{ab}} \to G^{\mathrm{ab}}$ induced by the inclusion (Milne, Proposition II.3.2(a)).
2. **Inflation–restriction.** If $H$ is normal, $r > 0$ and $H^j(H, M) = 0$ for $0 < j < r$, then
   $0 \to H^r(G/H, M^H) \to H^r(G, M) \to H^r(H, M)$, by inflation and restriction, is exact (Milne,
   Proposition II.1.34).
3. **Cup products.** The cup products $H^r(G, M) \times H^s(G, N) \to H^{r+s}(G, M \otimes N)$, with their
   compatibility with the connecting maps of exact sequences that stay exact after tensoring, and with restriction,
   corestriction and inflation (Milne, Propositions II.1.38 and II.1.39), and their extension to Tate cohomology; the identification
   $H^2(G, \mathbb{Z}) \cong \mathrm{Hom}(G, \mathbb{Q}/\mathbb{Z})$ by the connecting map of
   $0 \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z} \to 0$ (Milne, Lemma II.3.3(c)). For $G$ cyclic,
   cup product with the class $\delta\chi$ of an injective character $\chi \colon G \to \mathbb{Q}/\mathbb{Z}$
   is an isomorphism $\hat H^r(G, M) \to \hat H^{r+2}(G, M)$, a periodicity isomorphism (Milne, Remark
   II.3.5, which refers to Serre's *Local Fields*, VIII §4, for the proof).
4. **Tate's theorem.** If $H^1(H, M) = 0 = H^2(H, M)$ for every subgroup $H$ of $G$, then
   $\hat H^r(G, M) = 0$ for all $r$ (Milne, Theorem II.3.10). If $C$ is a $G$-module such that, for every
   subgroup $H$ of $G$, $H^1(H, C) = 0$ and $H^2(H, C)$ is cyclic of order $|H|$, then for every
   generator $\gamma$ of $H^2(G, C)$ cup product with $\gamma$ is an isomorphism
   $\hat H^r(G, \mathbb{Z}) \to \hat H^{r+2}(G, C)$ for all $r$; for $r = -2$ it is an isomorphism
   $G^{\mathrm{ab}} \to \hat H^0(G, C)$ (Milne, Theorem II.3.11 and Remark II.3.13). These isomorphisms
   commute with restriction and corestriction when the generators are compatible (Milne, the discussion
   after Theorem III.3.1).

5. **Products, unions and the trivial module.** Cohomology and Tate cohomology commute with products of
   $G$-modules (Milne, Proposition II.1.25) and with directed unions, or direct limits, of $G$-modules
   (Milne, Section II.4); for the trivial module, $\hat H^0(G, \mathbb{Z}) = \mathbb{Z}/|G|\mathbb{Z}$,
   $\hat H^{-1}(G, \mathbb{Z}) = 0$ (the norm is multiplication by $|G|$) and $H^1(G, \mathbb{Z}) = 0$
   (Milne, Lemma II.3.3(b)).

## Expansion

A good expansion has a page for each numbered item, splitting the first into the formula
$\mathrm{Cor} \circ \mathrm{Res} = (G : H)$ and its consequences.

## Depends on

- [Abelianization of a group](../../GroupTheory/commutators-and-engel-conditions/abelianization.md), for $G^{\mathrm{ab}}$ and $H^{\mathrm{ab}}$ and the map $H^{\mathrm{ab}} \to G^{\mathrm{ab}}$ in items 1 and 4
- [Tate cohomology groups of a finite group](tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md), for the Tate cohomology groups of a finite group, for all the items
- [Cup products in Tate cohomology](cup-products-in-tate-cohomology.md), for cup products, in items 3 and 4

## Proof depends on

- [Periodicity of Tate cohomology for finite cyclic groups](tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md), for the cyclic case of Tate's theorem

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>, Chapter II: Proposition 1.25, Example 1.29,
  Proposition 1.30, Corollaries 1.31–1.33, Proposition 1.34, Propositions 1.38 and 1.39; in Section 3,
  the extension of restriction, corestriction and Shapiro's lemma to Tate cohomology, Proposition 3.2,
  Lemma 3.3, Remark 3.5, Theorems 3.10 and 3.11 and Remark 3.13; Section 4 (direct limits); Section III.3,
  the discussion after Theorem 3.1.
