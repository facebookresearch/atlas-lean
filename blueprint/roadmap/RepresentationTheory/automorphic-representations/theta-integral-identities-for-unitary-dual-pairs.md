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
  the second. Only functions $\Phi'$ in a specified subspace $S^\circ$ of the Schwartz space of the
  second pair are matched: a pair $(\Phi, \Phi')$ is matched when $\Phi' \in S^\circ$ and both are
  finite sums of pure tensors that are limits of sums of pure tensors matched by these maps at each
  stage, with the approximants of $\Phi'$ in $S^\circ$.
- **Theta integral identities.** The theta integral $I(\Phi)$ converges for every Schwartz function
  $\Phi$ of the first pair; for $\Phi' \in S^\circ$ the theta function of the second pair decays
  rapidly, and $I'(\Phi')$ converges and has moderate growth. Convergence and equality are not
  asserted on the whole Schwartz space of the second pair. Some $\Phi' \in S^\circ$ has
  $I'(\Phi') \ne 0$, and there is exactly one constant $c$ with $I(\Phi)(h) = c\, I'(\Phi')(h)$ for
  all $h$ and all matched pairs $(\Phi, \Phi')$; it is nonzero. A statement on coinvariants
  accompanies it. When a hyperbolic
  plane is added to one of the spaces, the constants change by an explicit factor: a nonzero
  constant, values of $\nu$ at the fractional ideals of the added planes, local $\varepsilon$-factors
  of $\nu$ at the places of a finite set, and a value of the partial Hecke $L$-function of $\nu$ at a
  point determined by the dimensions.

These statements are held in this node because the geometries, models, matchings and
constants are defined by explicit lattice and character data specific to this proof, with many
side conditions (on the signatures, on the ramification of $E/F$ and of the characters, on the
additive character); a reviewable statement needs those definitions stated and checked first.

A good expansion has definition pages for the geometries, the Schrödinger models with their theta
integrals and the local matching maps; a page for each of the two statements, with the explicit
factor; and pages for the steps of their proof from the Siegel–Weil formula and from the properties
of Siegel Eisenstein series in the doubling method.

## Depends on

- [Splitting characters and the Weil representation of unitary dual pairs](theta-correspondence/weil-representation-of-unitary-dual-pairs.md), for unitary dual pairs and their Weil representations
- [Global Weil representation and theta functions](theta-correspondence/global-weil-representation-and-theta-functions.md), for theta functions
- [Weil's convergence criterion for theta integrals](theta-correspondence/weil-convergence-criterion.md), for theta integrals
- [Meromorphic continuation of Hecke L-functions](../../NumberTheory/zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for the partial Hecke $L$-values in the explicit factor

## Proof depends on

- [Siegel–Weil formula for unitary groups in Weil's convergent range](theta-correspondence/siegel-weil-formula-convergent-range.md), for its case of a definite space, which lies in the convergent range, and $K$-finite Schwartz functions, with the factor $1$ or $2$
- [Siegel Eisenstein series on unitary groups](theta-correspondence/siegel-eisenstein-series-on-unitary-groups.md), for the convergence of the Siegel Eisenstein series of flat sections in a right half-plane and their continuation (the first item there); the proof uses continuation in a stronger form, with at each point a pole-cleared family of functions of moderate growth that is holomorphic after every functional bounded on the functions of bounded polynomial growth, which that item does not state; it uses no statement on the location of the poles

## Sources

- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited by paths in it). The two statements are `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching` and `ThetaIntegralsAgree`, with the data `Base`, `Geo`, `Chars`, `IsTriple`, `IsMatched`, `Decay`, `OneConst`, `Coinv`, `StepBeta`, `StepAlpha` and `stepFac` of `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean`, lines 140–592. The matching `Match`, with $\Phi'$ in the subspace `G.M'.So B.ψ B.τ₁` and the approximating matched sums, and the constant `IsConst` are at lines 483–491 there; `Decay` (lines 498–501) gives convergence for every $\Phi$ and, for $\Phi'$ in that subspace only, rapid decay, convergence and moderate growth; `OneConst` (lines 503–505) gives the non-vanishing, the uniqueness and the non-vanishing of the constant; `LocalMatching` and `ThetaIntegralsAgree` are at lines 581–592. The partial Hecke $L$-values of the explicit factor are `charL X.ν X.S₀` in `StepBeta` and `StepAlpha` (lines 559–579 there). The library proves the two statements together as `UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`, lines 565–566), through `PositivityTheory.ThKR.theoremK_head2`, which consumes the statement `GlobalTheory.ThK.Dbl.EisBL` on Siegel Eisenstein series and the Siegel–Weil formula `GlobalTheory.ThK.Dbl.SiegelWeilStd` (lines 561–564 there). `SiegelWeilStd` is the formula for a definite space, $m, n \ge 1$, and $K$-finite Schwartz functions, with the factor $1$ if $n < m$ and $2$ otherwise (`src/Development/WeilBound/ThetaLifts/LatticeBasics/HypothesesS.lean`, lines 11–21); `EisBL` is the convergence of the Eisenstein series of a flat section in a right half-plane, with its holomorphy there, and, at each point $s_0$, a family $(s - s_0)^k E(s)$ in the span of the continuous functions of polynomial growth that is holomorphic after every functional bounded on the functions of each polynomial growth (`src/Development/WeilBound/ThetaLifts/LatticeBasics/HypothesesE.lean`, lines 40–53), not a statement on the location of the poles. They are consumed by the definite-side hypotheses at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean`, lines 44 and 49–54.
