# Model-category applications

The applications construct native spectrum models, models for higher
categories, and comparison adjunctions between their presentations. The
entry points expose named model choices, their morphism classes,
factorizations and derived comparisons. Select the named `ModelCategory`
locally when using a theorem about a particular model.

| Construction | Production entry points |
| --- | --- |
| Sequential, symmetric and orthogonal stable spectra | [Stable models](../MathlibExt/AlgebraicTopology/TopologicalSpace/Spectra/Native/StableModels.lean), [Sequential properties](../MathlibExt/AlgebraicTopology/TopologicalSpace/Spectra/Native/SequentialStableModelProperties.lean) |
| Stable smash products and monoid axioms | [Symmetric smash model](../MathlibExt/AlgebraicTopology/TopologicalSpace/Spectra/Native/NativeSymmetricStableMonoidalModel.lean), [Orthogonal smash model](../MathlibExt/AlgebraicTopology/TopologicalSpace/Spectra/Native/NativeOrthogonalStableMonoidalModel.lean), [All-object monoid axioms](../MathlibExt/AlgebraicTopology/TopologicalSpace/Spectra/Native/NativeAllObjectSpectrumMonoidAxiom.lean) |
| Spectrum index comparisons and positive level structure | [Stable index adjunctions](../MathlibExt/AlgebraicTopology/Spectra/IndexOperators/NativeStableAdjunctions.lean), [Positive level model](../MathlibExt/AlgebraicTopology/ModelCategory/EnrichedProjectiveNative/PositiveStabilizationK.lean) |
| Native module models and derived actions | [Symmetric module construction](../MathlibExt/AlgebraicTopology/ModelCategory/ModuleTransfer/NativeOriginalRankSources.lean), [Orthogonal module construction](../MathlibExt/AlgebraicTopology/ModelCategory/ModuleTransfer/NativeOrthogonalOriginalRankSources.lean), [Symmetric action](../MathlibExt/AlgebraicTopology/ModelCategory/ModuleTransfer/NativeDerivedAmbientAction.lean), [Orthogonal action](../MathlibExt/AlgebraicTopology/ModelCategory/ModuleTransfer/NativeOrthogonalDerivedAmbientAction.lean) |
| Joyal model and functor-core mapping spaces | [Joyal Cartesian model](../MathlibExt/AlgebraicTopology/SimplicialSet/JoyalCartesianModel.lean), [Derived functor cores](../MathlibExt/AlgebraicTopology/Quasicategory/FunctorCoreReplacementMapping.lean), [Relative equivalence transport](../MathlibExt/AlgebraicTopology/Quasicategory/FunctorCoreRelativeEquivalenceTransport.lean) |
| Native quasicategory pullbacks and pushouts | [Ordinary-nerve comparison](../MathlibExt/AlgebraicTopology/Quasicategory/NativePushout/Nerve.lean), [Pushout pasting](../MathlibExt/AlgebraicTopology/Quasicategory/NativePushout/Pasting.lean), [Pullback pasting with leg classes](../MathlibExt/AlgebraicTopology/Quasicategory/NativePullback/GridPastingClasses.lean) |
| Bergner model and coherent nerve | [Bergner model](../MathlibExt/AlgebraicTopology/SimplicialCategory/OriginalBergnerModelCategory.lean), [Coherent-nerve weak criterion](../MathlibExt/AlgebraicTopology/SimplicialCategory/CoherentNerveDwyerKan.lean), [Coherent comparison Quillen equivalence](../MathlibExt/AlgebraicTopology/SimplicialCategory/OriginalCoherentQuillenEquivalence.lean) |
| Rezk model and both Joyal–Tierney comparisons | [Complete Segal model](../MathlibExt/AlgebraicTopology/SimplicialSpace/RezkModelCategory.lean), [First comparison](../MathlibExt/AlgebraicTopology/SimplicialSpace/JoyalTierneyQuillenEquivalence.lean), [Total comparison](../MathlibExt/AlgebraicTopology/SimplicialSpace/TotalComparisonQuillenEquivalence.lean) |
| Completion, Segal recognition and functor spaces | [Intrinsic Dwyer–Kan recognition](../MathlibExt/AlgebraicTopology/SimplicialSpace/SegalIntrinsicDKRecognition.lean), [Derived mapping ends](../MathlibExt/AlgebraicTopology/SimplicialSpace/OriginalSmithCSSDerivedMapping.lean), [Complete Segal functor categories](../MathlibExt/AlgebraicTopology/SimplicialSpace/CompleteSegalFunctorCategory.lean) |
| Marked fixed-base models and straightening | [Cartesian and cocartesian models](../MathlibExt/AlgebraicTopology/SimplicialSet/Marked/ModelCategory.lean), [Coherent diagram model](../MathlibExt/AlgebraicTopology/SimplicialSet/Marked/CoherentDiagramModel.lean), [Straightening Quillen adjunction](../MathlibExt/AlgebraicTopology/SimplicialSet/Marked/NativeStraighteningOriginalQuillen.lean) |
| Integer cofiber and ordinary Puppe exactness | [Native symmetric cofiber sequence](../MathlibExt/AlgebraicTopology/Spectra/Symmetric/StableHomotopy/NativeCofiberIntegerExactness.lean), [Ordinary stable additivity](../MathlibExt/AlgebraicTopology/ModelCategory/OrdinaryStableHoAdditive.lean), [Integer Puppe complex](../MathlibExt/AlgebraicTopology/ModelCategory/OriginalOrdinaryIntegerPuppeComplex.lean) |

The API examples keep the named model choices, arbitrary arrows and their
class readbacks visible:

| Examples | API entry point |
| --- | --- |
| Sequential models, factorizations and index comparisons | [SequentialModelAPI](../MathlibExtTest/AlgebraicTopology/Spectra/SequentialModelAPI.lean) |
| Symmetric and orthogonal stable smash; positive level model | [SymmetricOrthogonalModelAPI](../MathlibExtTest/AlgebraicTopology/Spectra/SymmetricOrthogonalModelAPI.lean) |
| Joyal classes, fibrancy and Cartesian corners | [AtlasJoyalModelAPITest](../MathlibExtTest/AlgebraicTopology/SimplicialSet/AtlasJoyalModelAPITest.lean) |
| Varying-object Bergner factors and coherent comparison | [BergnerCoherentComparisonAPI](../MathlibExtTest/AlgebraicTopology/SimplicialCategory/BergnerCoherentComparisonAPI.lean) |
| Rezk classes, both Quillen equivalences and completion comparisons | [RezkComparisonAPI](../MathlibExtTest/AlgebraicTopology/SimplicialSpace/RezkComparisonAPI.lean) |
| Cartesian/cocartesian marked models and straightening adjunction | [MarkedModelAdjunctionAPI](../MathlibExtTest/AlgebraicTopology/ModelCategory/MarkedModelAdjunctionAPI.lean) |
| Ordinary stable additivity and integer exactness | [OrdinaryStablePuppeAPI](../MathlibExtTest/AlgebraicTopology/ModelCategory/OrdinaryStablePuppeAPI.lean) |

The native spectra are built over `PointedCGWH.{u, v}` with the concrete
sphere coordinate. Their generation and both small-object factorizations
use `realizedGeneratorCardinal.{v}` and the displayed
`OrderBot realizedGeneratorCardinal.ord.ToType`. Stable weak equivalences
are the full omega-testing class; stable cofibrations agree with level
cofibrations. Fibrant objects are the specified omega spectra. Sequential
stable weakness is equivalent to isomorphism on every integer homotopy
group, and its model is left and right proper. The separate generic
sequential **level** construction retains a cofibrant coordinate `T`,
coefficient generation at regular `κ`, sized colimits, local smallness,
and both source-colimit conditions.

Symmetric and orthogonal smash satisfy the pushout-product and Hovey unit
axioms for their named stable models. The unit witnesses retain their
chosen replacement maps and act on cofibrant spectrum factors. Their
monoid axioms allow arbitrary tensor factors and cellular size `w` under
`UnivLE.{w, v}`. The sequential/symmetric/orthogonal index adjunctions are
Quillen. Derived restrictions preserve and reflect stable weak maps;
the corresponding raw-restriction criteria retain fibrancy of both
endpoints. Positive symmetric indexing supplies the positive **level**
model, its generators and factorization data.

For any monoid object `A` in either native symmetric or orthogonal
carrier, the module constructors prove free-generator smallness at the
same realized cardinal and build the module model and replacements.
They prove relative flatness of cofibrant modules and scalar-change
Quillen equivalences for weak monoid maps. The derived ambient action
uses the constructed base and module models and has its associator and
unit coherence. Ordinary tensor computes that action when the displayed
coefficient and module are cofibrant; the general comparison uses both
chosen cofibrant replacements.

`JoyalSSet.{u}` has monomorphisms as cofibrations, categorical equivalences
as weak equivalences and categorical fibrations as fibrations. Fibrant
objects are precisely quasicategories. Cartesian pushout-product and
pullback-Hom laws hold. The inner-fibration/strict-equivalence-lifting
criterion for a map retains a quasicategory codomain. Functor-core
constructions prove Kan mapping spaces and natural derived comparisons;
the raw comparison to `core(Fun(Q A, R X))` is weak when `X` is fibrant.
Native pullback/pushout pasting uses an actual quasicategory and coherent
grids; ordinary nerve comparisons recover ordinary categorical squares
with their object and Hom universes unchanged.

The varying-object Bergner model on `Carrier.{u}` has enriched
Dwyer–Kan weak equivalences, local fibrations and the generated
cofibration class. Boundary and horn/interval constructions give its
functorial factors, with the native interval factorization at `aleph0`.
For locally Kan source and target enrichments, the coherent nerve of a
map is categorically weak exactly when its Hom maps are weak and the
induced homotopy-category functor is essentially surjective. Hom
fibrations give an inner fibration. For a locally Kan target, object
surjectivity and Hom trivial fibrations give a nerve trivial fibration. Coherent
realization and nerve form a Quillen equivalence between the named
Joyal and Bergner models in the same value universe. Its Hovey criterion
uses every cofibrant source, fibrant target and original adjunct arrow.

The Rezk model on `SimplicialSpace.{u}` constructs a regular common
generation cardinal, both generating families and factorizations.
Cofibrations are monomorphisms; weak equivalences are the fixed-universe
CSS mapping tests; fibrations are the right lifting class of monic Rezk
weak maps. Fibrant objects are exactly complete Segal spaces. The model
is combinatorial, Cartesian closed and left proper, with the full scalar
SM7 laws. Rezk fibrations are vertical Reedy fibrations; Rezk and Reedy
weakness agree on complete endpoints.

Both Joyal–Tierney adjunctions are Quillen equivalences. The first uses
the first-projection/inner-zero pair. The second uses the kernel
`Δ[n] × J[m]`, with `J[m]` the free-groupoid simplex. Each full weak-map
criterion keeps a cofibrant source, fibrant target and the actual
adjunct. Intrinsic Dwyer–Kan recognition applies to Reedy-fibrant Segal
spaces: mapping-fibre weakness and essential surjectivity characterize
Rezk weakness. Completion and coefficient-Smith replacements have
natural weak comparisons while retaining their independent choices.
Complete Segal functor/core identifications require both CSS endpoints;
target CSS alone gives the stated exponential fibrancy. These mapping
comparisons take values in ordinary localizations of Kan spaces and
ends. The Segal-groupoid delooping theorem uses a Reedy-fibrant Segal
space whose every edge is an equivalence.

The Cartesian and cocartesian marked models are constructed on
`Over (max B)` for every `B : SSet.{u}` with `Quasicategory B`.
Cofibrations are marked monomorphisms, weak classes use the full
intrinsic relative mapping tests, and fibrant objects are the intrinsic
Cartesian or cocartesian fibrations with their full markings. The
coherent projective target is indexed by `(realization B)ᵒᵖ` and exists
for every simplicial base. Over a quasicategory base, native
straightening/unstraightening is a Quillen adjunction; unstraightening
preserves model fibrations and trivial fibrations without endpoint
diagram-fibrancy assumptions.

Native integer cofiber exactness applies to the actual Q-cofiber of each
spectrum arrow. Ordinary additivity, finite biproducts and Puppe
exactness have a separate stability hypothesis. They use a pointed
model category, `HasLimitsOfSize.{0, v}` and
`HasColimitsOfSize.{0, v}`, generation data `g` at regular `κ` with
ordinal bottom, and

```lean
(DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence
```

The integer Puppe complex also keeps a chosen zero `Z`, its `IsZero`
proof, the homotopy-category arrow and a specified limiting pullback
cone for its fibration projection. Under these hypotheses the Hom
groups and boundary maps are additive, all three integer exact
positions hold, and the coefficient complex is acyclic with zero
homology. Topological comparisons retain their pointed CGWH enrichment
and compatible model action.
