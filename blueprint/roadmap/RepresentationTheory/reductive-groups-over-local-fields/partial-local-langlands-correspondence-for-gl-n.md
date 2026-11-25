# Partial local Langlands correspondence for GLₙ over completions of number fields

This node is still to be broken down. It covers the existence of a partial local Langlands
correspondence at each finite place of a number field, with the laws that the
[Galois representations attached to polarized cuspidal representations](../../NumberTheory/algebraic-number-theory/galois-representations/galois-representations-attached-to-polarized-cuspidal-representations.md)
and the
[definite-side hypotheses](../automorphic-representations/definite-side-hypotheses-for-character-families.md)
refer to. Let $E$ be a number field, $v$ a finite place of $E$ with completion $E_v$, and fix a place of
an algebraic closure of $E$ above $v$, which determines the Weil group $W_{E_v}$. Then there are a local
Artin map $a \colon W_{E_v} \to E_v^\times$ and a map $\mathrm{rc}$ from the isomorphism classes of
irreducible smooth complex representations of the groups $\mathrm{GL}_n(E_v)$, $n \ge 0$, to
Weil–Deligne representations of $W_{E_v}$, with the following laws:

- $\mathrm{rc}(\pi)$ has dimension $n$ for $\pi$ a representation of $\mathrm{GL}_n(E_v)$, and
  $\mathrm{rc}(\chi) = \chi \circ a$ for a smooth character $\chi$ of $E_v^\times$;
- compatibility with the Langlands classification: if $\pi$ is attached to a multiset of segments
  $\Delta$, each with first cuspidal representation $\rho_\Delta$ and length $m_\Delta$, then
  $\mathrm{rc}(\pi)$ is the direct sum, over the segments, of the tensor products with
  $\mathrm{Sp}(m_\Delta)$ of the unramified twists of exponent $(m_\Delta - 1)/2$ of
  $\mathrm{rc}(\rho_\Delta)$;
- $\mathrm{rc}$ sends cuspidal representations to irreducible Weil–Deligne representations and
  the twists $\pi \otimes |\det|^s$ to the unramified twists of exponent $s$, and the absolute value
  of the determinant of $\mathrm{rc}(\pi)(\sigma)$ is that of the central character of $\pi$ at
  $a(\sigma)$;
- for the "good" representations, those whose cuspidal support consists of characters or, when
  $E_v \cong \mathbb{Q}_g$, of twists by characters of depth-zero cuspidal representations:
  compatibility with twists by characters, with central characters and with contragredients,
  injectivity, and tameness of $\mathrm{rc}(\pi)$ when $\pi$ has depth zero;
- a type law: when $E_v \cong \mathbb{Q}_g$, for an irreducible smooth representation of
  $\mathrm{GL}_n(\mathbb{Q}_g)$ containing the inflation of the cuspidal representation of
  $\mathrm{GL}_n(\mathbb{F}_g)$ attached by Green to a regular character $\theta$ of
  $\mathbb{F}_{g^n}^\times$, the image under $\mathrm{rc}$ has zero monodromy, and on the inertia
  subgroup of the Weil group of the unramified extension of degree $n$ its characteristic polynomials
  are $\prod_{j=0}^{n-1} (X - \theta(z^{g^j}))$, where $z$ is the residue of the local Artin map of
  that extension.

The local Langlands correspondence for $\mathrm{GL}_n$ satisfies laws of this kind for all
representations; the form covered here asks less, except for the explicit type law. It is held as a
node because the laws are formulated with encodings specific to this proof of
Weil–Deligne representations (dimension, twists, tensor products with characters and with
$\mathrm{Sp}(m)$, duals, characteristic polynomials of inertia, monodromy) and of local Artin maps;
a reviewable statement needs each encoding stated and checked first.

A good expansion has a page for the precise statement of the laws, a page comparing them with the
local Langlands correspondence, and pages for the construction that the proof below follows: a
local Artin map obtained from the global Artin map, a correspondence on cuspidal representations
built from cuspidal parameters, and its extension to all irreducible representations through the
Langlands classification.

## Depends on

- [Smooth and admissible representations of p-adic groups](representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for irreducible smooth representations
- [Cuspidal representations and Jacquet's embedding theorem](representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for cuspidal representations
- [Uniqueness of cuspidal support](representations-of-p-adic-reductive-groups/uniqueness-of-cuspidal-support.md), for the cuspidal support of an irreducible representation, in the definition of the "good" representations
- [Zelevinsky's classification of the irreducible representations of GLₙ](representations-of-p-adic-gl-n/zelevinsky-classification.md), for segments
- [Langlands classification for GLₙ](representations-of-p-adic-gl-n/langlands-classification-for-gl-n.md)
- [Depth and unrefined minimal K-types](representations-of-p-adic-reductive-groups/depth-and-unrefined-minimal-k-types.md), for depth
- [Weil group of a p-adic field](../../NumberTheory/algebraic-number-theory/galois-representations/weil-deligne-representations/weil-group-of-a-p-adic-field.md), for Weil groups
- [Weil–Deligne representations](../../NumberTheory/algebraic-number-theory/galois-representations/weil-deligne-representations/weil-deligne-representations.md)
- [Green's parametrization of the cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_q)$](../../GroupTheory/characters-of-finite-groups/green-cuspidal-characters-of-gl-n.md), for the case of a prime field, in the type law

## Proof depends on

- [Cuspidal representations and Jacquet's embedding theorem](representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for Jacquet's embedding theorem, by which every irreducible representation has a cuspidal support, and for the admissibility of irreducible representations, used for the representations of the correspondence constructed from cuspidal parameters
- [Finite length of parabolically induced representations](representations-of-p-adic-reductive-groups/finite-length-of-induced-representations.md), for the finite length of the products of representations of the groups $\mathrm{GL}_n$ that the correspondence uses
- [Zelevinsky's classification of the irreducible representations of GLₙ](representations-of-p-adic-gl-n/zelevinsky-classification.md), for the segments and the polynomial structure of the Grothendieck ring that the correspondence uses
- [Langlands classification for GLₙ](representations-of-p-adic-gl-n/langlands-classification-for-gl-n.md), for the extension of the correspondence from cuspidal representations to all irreducible representations through multisets of segments, with the uniqueness of the multiset, the contragredients and the composition factor $L(a + b)$ of $L(a) \times L(b)$
- [Uniqueness of cuspidal support](representations-of-p-adic-reductive-groups/uniqueness-of-cuspidal-support.md), for the uniqueness of the cuspidal support of an irreducible representation of $\mathrm{GL}_n$, by which the correspondence compares the supports it uses
- [Depth under parabolic induction and Jacquet functors](representations-of-p-adic-reductive-groups/depth-under-parabolic-induction-and-jacquet-functors.md), for the depth of the members of a cuspidal support (Moy–Prasad), by which every member of the support of a representation of $\mathrm{GL}_n$ with nonzero vectors fixed by the principal congruence subgroup has such vectors too, used for the depth-zero representations of the correspondence
- [Global Artin map](../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reciprocity-law/global-artin-map.md), for the global Artin map and its uniqueness as the continuous homomorphism with prescribed restrictions to the local multiplicative groups; the uniqueness that the proof uses is a different statement, for a map with the properties of the reciprocal global Artin map listed on the next page, which the proof derives from those properties, and it is not the norm-quotient law of the global reciprocity law either. From the global map the proof constructs the local map $a \colon W_{E_v} \to E_v^\times$ as a surjective homomorphism, continuous on inertia and compatible with the global map on the decomposition group; this local map, defined on the Weil group, is not the pointwise reciprocal of the global Artin map, which is defined on idèles
- [The global Artin map on the Galois group of the maximal abelian extension](../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reciprocity-law/artin-map-on-the-maximal-abelian-extension.md), for the properties at infinite level that the construction of the local map uses, in the reciprocal normalization, in which uniformizers go to geometric Frobenius elements: the surjectivity, openness and kernel of the map and its behaviour on the inertia and decomposition groups

## Sources

- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited by paths in it). The node is `UpperTheory.Zero.LLC.RecTExists`, with the laws `LawsT`, the good representations `Good` and `GoodCusp`, and the type law `TypeLaw` (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean`, lines 20–80), and `GlobalTheory.LocLanglands.segSum` for the Langlands classification (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/Langlands.lean`, lines 17–18). The library proves it as `UpperTheory.Zero.LLC.recTExists` (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean`, lines 20–66) from the local Artin map `UpperTheory.Zero.LLC.artEx` (line 23), the cuspidal parameters `UpperTheory.Zero.LLC.cuspEx` (line 24; `.../LocalCentralUnits/CuspEx.lean`, line 168) and their extension `GlobalTheory.LocLanglands.exists_isLExt` through the Langlands classification (line 26), with the classification's exhaustion and multisegments `UpperTheory.Zero.LLC.Pr.exh` and `Pr.multi` (`.../LocalLanglands/Multi.lean`, lines 11–12). The global Artin map is consumed in `GlobalTheory.localArtinExists_holds` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalArtinExistsHolds.lean`, lines 56–69): `globalArtinReciprocity_holds` at line 58, the construction from it of a compatible local homomorphism from the Weil group to $E_v^\times$ (`exists_inverse_localArtin_weilGroup_hom`, line 59), a map with another domain than the global Artin map and not obtained by inverting its values, the continuity of that local map on inertia at line 60, and, at line 68, the uniqueness of a map with the properties of the reciprocal global Artin map, `GlobalTheory.T.globalArtinReciprocityMap_unique` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalArtinReciprocityMapUniqueStatement.lean`, line 11), proved as `GlobalTheory.ArtinUniq.globalArtin_unique` (`GlobalArtinReciprocityMapUnique.lean` in the same folder, lines 137ff.) for the maps that satisfy `IsGlobalArtin` (`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean`, lines 25–39: an open quotient map whose kernel is the closure of the principal idèles times the identity component at the infinite places, mapping the units at each finite place onto the inertia groups, the uniformizers to the inverses of Frobenius elements, and the local multiplicative groups densely into the decomposition groups). This uniqueness is neither the uniqueness of the global Artin map given its local restrictions nor the norm-quotient law of the global reciprocity law. The node is consumed by the definite-side hypotheses (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean`, lines 44 and 73, supplied at `.../ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`, line 813), and its laws by the Galois representations attached to polarized cuspidal representations (`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`, line 7).
