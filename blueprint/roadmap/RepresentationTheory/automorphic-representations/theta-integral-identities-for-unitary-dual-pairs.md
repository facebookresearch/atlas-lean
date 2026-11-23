# Theta integral identities and local matching for unitary dual pairs

This node is still to be broken down. It covers two statements about the theta integrals of unitary
dual pairs over a CM extension $E/F$ of number fields, in explicit Schrödinger models, which the
[definite-side hypotheses](definite-side-hypotheses-for-character-families.md) use. The data are a
geometry, made of Hermitian spaces of dimensions $a$ and $a'$ and a skew-Hermitian space of dimension
$a + a'$ over $E$ with their signatures at the real places and their lattices at the finite places;
Hecke characters $\alpha$ and $\beta$ of $E$, with $\nu = \alpha/\beta$, and finite sets of places; and
Weil representations $\omega$ and $\omega'$ of the two dual pairs that share the skew-Hermitian space.

- **Local matching.** For such data there are maps at the real places and at the finite places
  that match Schwartz functions $\Phi$ for the first dual pair with Schwartz functions $\Phi'$ for
  the second.
- **Theta integral identities.** The theta integrals $I(\Phi)$ and $I'(\Phi')$ of the two pairs
  converge, and for matched $\Phi$ and $\Phi'$ they agree up to a single nonzero constant,
  $I(\Phi)(h) = c\, I'(\Phi')(h)$ for all $h$, with a statement on coinvariants. When a hyperbolic
  plane is added to one of the spaces, the constants change by an explicit factor: a nonzero
  constant, values of $\nu$ at the fractional ideals of the added planes, local $\varepsilon$-factors
  of $\nu$ at the places of a finite set, and a value of the partial Hecke $L$-function of $\nu$ at a
  point determined by the dimensions.

These statements are not yet stated as pages because the geometries, models, matchings and
constants are defined by explicit lattice and character data specific to this proof, with many
side conditions (on the signatures, on the ramification of $E/F$ and of the characters, on the
additive character); a reviewable statement needs those definitions stated and checked first.

A good expansion has definition pages for the geometries, the Schrödinger models with their theta
integrals and the local matching maps; a page for each of the two statements, with the explicit
factor; and pages for the steps of their proof from the Siegel–Weil formula and from the properties
of Siegel Eisenstein series in the doubling method.

## Depends on

- [Theta correspondence for unitary dual pairs](theta-correspondence-for-unitary-dual-pairs.md), for unitary dual pairs, Weil representations, theta functions and theta integrals
- [Meromorphic continuation of Hecke L-functions](../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for the partial Hecke $L$-values in the explicit factor

## Proof depends on

- [Theta correspondence for unitary dual pairs](theta-correspondence-for-unitary-dual-pairs.md), for the Siegel–Weil formula and the Siegel Eisenstein series of the doubling method

## Sources

- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited by paths in it). The two statements are `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching` and `ThetaIntegralsAgree`, with the data `Base`, `Geo`, `Chars`, `IsTriple`, `IsMatched`, `Decay`, `OneConst`, `Coinv`, `StepBeta`, `StepAlpha` and `stepFac` of `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean`, lines 140–592. The partial Hecke $L$-values of the explicit factor are `charL X.ν X.S₀` in `StepBeta` and `StepAlpha` (lines 559–579 there). The library proves the two statements together as `UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`, lines 565–566), through `PositivityTheory.ThKR.theoremK_head2`, which consumes the statement `GlobalTheory.ThK.Dbl.EisBL` on Siegel Eisenstein series and the Siegel–Weil formula `GlobalTheory.ThK.Dbl.SiegelWeilStd` (lines 561–564 there). They are consumed by the definite-side hypotheses at `SiegelEisensteinSecondTermHypotheses.lean`, in the same folder, lines 44 and 49–54.
