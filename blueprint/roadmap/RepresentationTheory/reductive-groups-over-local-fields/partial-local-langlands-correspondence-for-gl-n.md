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
representations; the form covered here asks less, except for the explicit type law. It is not yet
stated as a page because the laws are formulated with encodings specific to this proof of
Weil–Deligne representations (dimension, twists, tensor products with characters and with
$\mathrm{Sp}(m)$, duals, characteristic polynomials of inertia, monodromy) and of local Artin maps;
a reviewable statement needs each encoding stated and checked first.

A good expansion has a page for the precise statement of the laws, a page comparing them with the
local Langlands correspondence, and pages for the construction that the proof below follows: a
local Artin map obtained from the global Artin map, a correspondence on cuspidal representations
built from cuspidal parameters, and its extension to all irreducible representations through the
Langlands classification.

## Depends on

- [Smooth representations of p-adic GLₙ and the local Langlands correspondence](smooth-representations-of-p-adic-gl-n-and-local-langlands.md), for irreducible smooth representations, cuspidal supports, segments, the Langlands classification and depth
- [Galois cohomology and p-adic Hodge theory](../../NumberTheory/galois-representations/galois-cohomology-and-p-adic-hodge-theory.md), for Weil groups and Weil–Deligne representations
- [Green's parametrization of the cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_q)$](../../GroupTheory/characters-of-finite-groups/green-cuspidal-characters-of-gl-n.md), for the case of a prime field, in the type law

## Proof depends on

- [Smooth representations of p-adic GLₙ and the local Langlands correspondence](smooth-representations-of-p-adic-gl-n-and-local-langlands.md), for a partial local Langlands correspondence constructed from cuspidal parameters and extended through the Langlands classification
- [Global Artin reciprocity](../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/global-artin-reciprocity.md), for the global Artin map and its uniqueness, from which the local map $a \colon W_{E_v} \to E_v^\times$ is constructed as a surjective homomorphism, continuous on inertia and compatible with the global Artin map on the decomposition group; this local map, defined on the Weil group, is not the pointwise reciprocal of the global Artin map, which is defined on idèle classes

## Sources

- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited by paths in it). The node is `UpperTheory.Zero.LLC.RecTExists`, with the laws `LawsT`, the good representations `Good` and `GoodCusp`, and the type law `TypeLaw` (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean`, lines 20–80), and `GlobalTheory.LocLanglands.segSum` for the Langlands classification (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/Langlands.lean`, lines 17–18). The library proves it as `UpperTheory.Zero.LLC.recTExists` (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean`, lines 20–66) from the local Artin map `UpperTheory.Zero.LLC.artEx` (line 23), the cuspidal parameters `UpperTheory.Zero.LLC.cuspEx` (line 24; `.../LocalCentralUnits/CuspEx.lean`, line 168) and their extension `GlobalTheory.LocLanglands.exists_isLExt` through the Langlands classification (line 26), with the classification's exhaustion and multisegments `UpperTheory.Zero.LLC.Pr.exh` and `Pr.multi` (`.../LocalLanglands/Multi.lean`, lines 11–12). The global Artin map is consumed in `GlobalTheory.localArtinExists_holds` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalArtinExistsHolds.lean`, lines 56–69): `globalArtinReciprocity_holds` at line 58, the construction from it of a compatible local homomorphism from the Weil group to $E_v^\times$ (`exists_inverse_localArtin_weilGroup_hom`, line 59), a map with another domain than the global Artin map and not obtained by inverting its values, the continuity of that local map on inertia at line 60, and the uniqueness of the global Artin map at line 68. The node is consumed by the definite-side hypotheses (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean`, lines 44 and 73, supplied at `.../ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`, line 813), and its laws by the Galois representations attached to polarized cuspidal representations (`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`, line 7).
