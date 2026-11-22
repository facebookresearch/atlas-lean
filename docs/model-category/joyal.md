# The Joyal model and quasicategory APIs

The Joyal model is provided on `JoyalSSet`, a native copy of simplicial sets.
Its ordinary forgetful equivalence preserves the underlying simplicial maps.
The designated carrier keeps the Joyal model separate from the Kan–Quillen
model on `SSet`.

```lean
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalCartesianModel
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.AllCofibrant
import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral
import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreHomotopyInvariance
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.RightMappingBrown
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKanRecognition
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.NerveGate

open scoped JoyalSSet.ModelCategory
```

For the named model, cofibrations are monomorphisms, weak equivalences are
categorical equivalences of the underlying maps, and fibrations are the full
right lifting class of monic categorical equivalences. Fibrant objects are
exactly quasicategories. The model is combinatorial and every object is
cofibrant.

The construction uses the finite Joyal interval and its concrete Smith
recognition input. Both weak factorization systems and a common cardinal for
local presentability and generation are conclusions of the construction.
`JoyalSSet.exists_joyal_modelCategory` retains that complete witness.

The Cartesian tensor is closed and symmetric. The theorem
`JoyalSSet.isClosedSymmetricMonoidalModelCategory` supplies the three
pushout-product laws and the cofibrant-unit axiom for this same model.
Its weak tensor factors are categorical weak equivalences. It does not supply
compatibility with arbitrary Kan-trivial tensor factors.

The fibration criterion by inner fibrations and homotopy-category
isofibrations requires a quasicategory codomain. For an arbitrary codomain,
use `SSet.categoricalFibrations`, defined by the full lifting condition.

| API | Scope |
| --- | --- |
| `JoyalSSet.modelCategory` and its three classifier theorems | The complete named model on the designated carrier. |
| `JoyalSSet.isFibrant_iff_quasicategory` | Every designated object. |
| `SSet.categoricalFibrations_and_categoricalEquivalences_iff` | Full boundary-RLP criterion for arbitrary simplicial maps. |
| `SSet.categoricalFibrations_iff_innerFibration_and_hoIsofibration` | Quasicategory codomain. |
| `SSet.kanComplex_core_of_quasicategory` | Quasicategory source; provided by `SpecialOuterHornGeneral`. |
| `SSet.FunctorCore.mapBoth_weak` | Categorical equivalences in both variables and quasicategory targets. |
| `SSet.categoricalEquivalences.rightMappingSpaceMap_weak` | Categorical equivalence between quasicategories and arbitrary endpoint pairs. |
| `SSet.categoricalEquivalences_iff_isDwyerKanEquivalence` | Quasicategory endpoints; the actual same-endpoint right mapping spaces. |
| `SSet.categoricalEquivalences_nerveMap_iff` | Ordinary categories in the theorem's stated object and hom universe. |

Categorical weak equivalences test precomposition into every quasicategory
in the stated value universe. The mapping-space and functor-core APIs retain
their source, target and universe hypotheses. Earlier conditional comparison
lemmas keep their additional assumptions; the unconditional right-mapping
recognition is provided by `RightMappingBrown` and `DwyerKanRecognition`.

`MathlibExtTest.AlgebraicTopology.SimplicialSet.AtlasJoyalModelAPITest` exercises
the model classes, both trivial pushout-product orientations, full diagonal
equations, the fibration criterion and its codomain restriction. A directed
category's nerve supplies a concrete Joyal-fibrant object which is not Kan.
The surrounding tests cover the finite interval, cores, equivalence edges
and mapping-space constructions.

The separate Bergner/coherent-nerve and Joyal–Tierney/Rezk comparison
packages are not required by these imports.

References:

- J. Lurie, *Higher Topos Theory*, §2.2.5 and §2.4.6,
  [arXiv:math/0608040](https://arxiv.org/abs/math/0608040).
- D. Stevenson, *Notes on the Joyal model structure*, §2.4,
  [arXiv:1810.05233](https://arxiv.org/abs/1810.05233).
- D.-C. Cisinski, *Higher Categories and Homotopical Algebra*, the finite
  interval and model-recognition development.
- A. Campbell, *A counterexample in quasi-category theory*,
  [arXiv:1904.04965](https://arxiv.org/abs/1904.04965), for the codomain boundary
  of the inner/isofibration criterion.
