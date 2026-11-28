# Change of the group

The maps of [cohomology](../cohomology-with-discrete-coefficients.md) of profinite groups with discrete coefficients
under a change of the group, following Neukirch–Schmidt–Wingberg, Chapter I, §5 and §6. A compatible pair
$\varphi \colon G' \to G$, $f \colon A \to A'$ induces $H^n(G, A) \to H^n(G', A')$
([Cohomology commutes with direct limits](../cohomology-commutes-with-direct-limits.md) states it); its cases are the
conjugation $\sigma_*$, inflation $\inf \colon H^n(G/H, A^H) \to H^n(G, A)$ for a closed normal subgroup $H$ and
restriction $\operatorname{res} \colon H^n(G, A) \to H^n(H, A)$ for a closed subgroup $H$, and there is a
corestriction $\operatorname{cor} \colon H^n(U, A) \to H^n(G, A)$ for an open subgroup $U$. The pages state their
properties, the action of $G/H$ on $H^n(H, A)$ for $H$ normal, and the transgression; the compatibility with cup
products (Proposition (1.5.3)) is planned with the [cup products](../cup-products.md).

The first pages state restriction and corestriction for a subgroup of finite index of an abstract group, on Mathlib's
group cohomology `groupCohomology`, and their extension to Tate cohomology of a finite group: these give the
annihilation of cohomology by the order of a finite group. Mathlib's `groupCohomology.map` is the map induced by a
compatible pair, `groupCohomology.resNatTrans` and `groupCohomology.infNatTrans` are restriction and inflation,
`groupCohomology.coindIso` is Shapiro's lemma for coinduction, and `groupCohomology.H1InfRes_exact` is the exactness of
inflation and restriction in degree one.

## Subgroups of finite index of abstract groups

- [Restriction through Shapiro's lemma](restriction-through-shapiro-s-lemma.md)
- [Corestriction for subgroups of finite index](corestriction-for-subgroups-of-finite-index.md)
- [The coinduction unit followed by the norm is multiplication by the index](unit-followed-by-norm-is-the-index.md)
- [Corestriction after restriction for subgroups of finite index](corestriction-after-restriction-for-subgroups-of-finite-index.md)

## Tate cohomology of finite groups

- [Shapiro's lemma for Tate cohomology](shapiro-s-lemma-for-tate-cohomology.md)
- [Restriction and corestriction on Tate cohomology](restriction-and-corestriction-on-tate-cohomology.md)
- [Corestriction after restriction on Tate cohomology](corestriction-after-restriction-on-tate-cohomology.md)

## Profinite groups

- [Inflation, restriction and conjugation](inflation-restriction-and-conjugation.md)
- [Corestriction for open subgroups](corestriction.md)
- [Restriction through Shapiro's lemma for profinite groups](restriction-through-shapiro-s-lemma-for-profinite-groups.md)
- [The cochain formula for corestriction](cochain-formula-for-corestriction.md)
- [Corestriction after restriction](corestriction-after-restriction.md)
- [Transitivity of inflation, restriction and corestriction](transitivity-of-inflation-restriction-and-corestriction.md)
- [Functoriality and the connecting homomorphisms](functoriality-and-connecting-homomorphisms.md)
- [Conjugation commutes with inflation, restriction and corestriction](conjugation-commutes-with-inflation-restriction-and-corestriction.md)
- [Inflation commutes with restriction and corestriction](inflation-commutes-with-restriction-and-corestriction.md)
- [The double coset formula](double-coset-formula.md)
- [Restriction after corestriction](restriction-after-corestriction.md)
- [The action of the quotient on the cohomology of a normal subgroup](action-of-the-quotient-on-the-cohomology-of-a-normal-subgroup.md)
- [The transgression](transgression.md)
- [Change of the group for continuous cochain cohomology](change-of-group-for-continuous-cochain-cohomology.md)

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §5, pp. 45–51, Propositions
  (1.5.2)–(1.5.6) and Corollary (1.5.7); Chapter I, §6, Propositions (1.6.3)–(1.6.6), pp. 61–66; Chapter II, §7,
  p. 138.
- J. S. Milne, *Class Field Theory*, version 4.03 (2020), <https://www.jmilne.org/math/CourseNotes/CFT.pdf>:
  Chapter II, Example 1.29 and Proposition 1.30, p. 70; Chapter II, §3, the extension of restriction and corestriction
  to Tate cohomology, p. 79.
