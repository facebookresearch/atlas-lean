/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.AlgebraInCategory
import Atlas.TensorCategories.code.AlgebrasInCategories
import Atlas.TensorCategories.code.AlgebrasInCategoriesDefs
-- import Formalization.AlgebrasInCategoriesDefsBatch  -- commented out: conflicts with other imports
-- import Formalization.AntipodeBijective.Assembly  -- commented out: conflicts with other imports
-- import Formalization.AntipodeBijective.Injective  -- commented out: conflicts with other imports
-- import Formalization.AntipodeBijective.RankEquality  -- commented out: conflicts with other imports
-- import Formalization.BasedRings  -- commented out: conflicts with other imports
-- import Formalization.BasedRingsGeneral  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.BasicMonoidalDefs

import Atlas.TensorCategories.code.Bimodule

-- import Formalization.CartierKostant.Axioms  -- commented out: conflicts with other imports
-- import Formalization.CartierKostant.CommHopfFunGroup  -- commented out: conflicts with other imports
-- import Formalization.CartierKostant.Theorems  -- commented out: conflicts with other imports
-- import Formalization.CartierKostant  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.CategoricalDimension
-- import Formalization.CategoricalFreeness  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.Ch1Theorems
import Atlas.TensorCategories.code.ChevalleyProperty
-- import Formalization.ChevalleyTheorem -- commented out: Mathlib API change (IsSemisimpleModule.jacobson_eq_bot)
import Atlas.TensorCategories.code.CoalgebraBialgebra
-- import Formalization.CocommutativeMonoidAlgebra  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.ComoduleDuals
-- import Formalization.ConcreteInstances  -- commented out: conflicts with other imports

-- import Formalization.ConcreteModuleCategories  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.CoradicalFiltration
import Atlas.TensorCategories.code.Corollary_1_13_4
import Atlas.TensorCategories.code.Corollary_1_13_7
import Atlas.TensorCategories.code.Corollary_1_15_2
import Atlas.TensorCategories.code.Corollary_1_15_9
import Atlas.TensorCategories.code.Corollary_1_22_6

-- import Formalization.Corollary_1_29_7  -- commented out: conflicts with other imports

-- import Formalization.Corollary_1_43_5  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_43_6  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.Corollary_1_45_11

-- import Formalization.Corollary_1_50_3  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_50_4  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_51_3  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_51_5  -- commented out: conflicts with other imports
-- import Formalization.Corollary_2_10_5  -- commented out: conflicts with other imports
-- import Formalization.Corollary_2_14_9  -- commented out: conflicts with other imports

import Atlas.TensorCategories.code.Definition_1_15_4
import Atlas.TensorCategories.code.Definition_1_18_1
import Atlas.TensorCategories.code.Definition_1_18_2
-- import Formalization.Definition_1_22_2  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.Definition_1_34_1
import Atlas.TensorCategories.code.Definition_1_45_7
import Atlas.TensorCategories.code.Definition_1_46_1
-- import Formalization.Definition_1_52_1  -- commented out: conflicts with other imports
-- import Formalization.Definition_1_52_6  -- commented out: conflicts with other imports
-- import Formalization.Definition_1_5_1  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.Definition_2_1_6
import Atlas.TensorCategories.code.Definition_2_3_1
-- import Formalization.Definition_2_5_4  -- commented out: conflicts with other imports

import Atlas.TensorCategories.code.Definition_2_9_18_ExactAlgebra
-- import Formalization.Definition_2_9_21  -- commented out: conflicts with other imports
-- import Formalization.Definition_2_9_22  -- commented out: conflicts with other imports
-- import Formalization.Definition_2_9_24  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.DeligneTensorProduct
import Atlas.TensorCategories.code.DeligneTensorProductDef

import Atlas.TensorCategories.code.DirectSumModuleCategory
import Atlas.TensorCategories.code.DirectSumModuleCategoryDef
-- import Formalization.DistinguishedInvertible  -- commented out: conflicts with other imports
-- import Formalization.DrinfeldCenter  -- commented out: conflicts with other imports
-- import Formalization.DualCatDefs  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.DualCategory
import Mathlib
import Atlas.TensorCategories.code.DualDefinitions
import Atlas.TensorCategories.code.EndTensorProduct
-- import Formalization.ExactAlgebra  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.ExactModuleCatEquiv
import Atlas.TensorCategories.code.ExactModuleCategory
import Atlas.TensorCategories.code.ExactModuleCriteria
import Atlas.TensorCategories.code.ExactModuleProjectives
import Atlas.TensorCategories.code.Ext1UnitVanishing
import Atlas.TensorCategories.code.FPdimCategory
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Atlas.TensorCategories.code.FPdimProps
import Atlas.TensorCategories.code.FiberFunctor
import Atlas.TensorCategories.code.FiberFunctorEnd
import Atlas.TensorCategories.code.FiniteAbelianCategoryDef

import Atlas.TensorCategories.code.FiniteTensorCategory
import Atlas.TensorCategories.code.FittingAlgebraLocalRing
import Atlas.TensorCategories.code.FittingLemmaInstance
import Atlas.TensorCategories.code.FittingLemmaLocalEnd
import Atlas.TensorCategories.code.FrobeniusPerron
import Atlas.TensorCategories.code.GradedVec
import Atlas.TensorCategories.code.GrothendieckFusionRingInstance
import Atlas.TensorCategories.code.GrothendieckModuleIrreducible
import Atlas.TensorCategories.code.GrothendieckRing
import Atlas.TensorCategories.code.GrothendieckRingCategorical
import Atlas.TensorCategories.code.GrothendieckRingHom
import Atlas.TensorCategories.code.GroupoidMultitensor
import Atlas.TensorCategories.code.HigherDerivation
import Atlas.TensorCategories.code.HomExactImpliesExact
import Atlas.TensorCategories.code.HopfAlgebra
import Atlas.TensorCategories.code.HopfAlgebraAntiHom
import Atlas.TensorCategories.code.HopfAlgebraExamples
import Atlas.TensorCategories.code.HopfAlgebraRep
-- import Formalization.HopfAlgebraRigid  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.IndecomposableModuleCat
import Atlas.TensorCategories.code.Instances.VecFiniteTensorCategory
import Atlas.TensorCategories.code.IntegralCategories
-- import Formalization.IntegralsCartanMatrix  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.IntegralsClean
-- import Formalization.IntegralsDefs  -- commented out: conflicts with other imports
-- import Formalization.IntegralsProps  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.InternalHom
-- import Formalization.InternalHomEssSurjInstance  -- commented out: conflicts with other imports
-- import Formalization.InternalHomFaithfulInstance  -- commented out: conflicts with other imports
-- import Formalization.InternalHomFullInstance  -- commented out: conflicts with other imports
-- import Formalization.InternalHomFunctor  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.InvertibleObjects
import Atlas.TensorCategories.code.K0Bimodule
import Atlas.TensorCategories.code.Lemma285
import Atlas.TensorCategories.code.Lemma_1_30_2
-- import Formalization.Lemma_1_33_2  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.Lemma_1_51_1
import Atlas.TensorCategories.code.Lemma_2_13_2

-- import Formalization.Lemma_2_14_10  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.Lemma_2_14_7
import Atlas.TensorCategories.code.Lemma_2_8_5
-- import Formalization.Lemma_2_9_12  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.LocalEndRingsInstance
import Atlas.TensorCategories.code.LocallyFiniteDefs
import Atlas.TensorCategories.code.MacLaneCoherence
import Atlas.TensorCategories.code.MacLaneStrictness
-- import Formalization.MfStarAlgebra  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.ModuleCategory.Theorem2112
import Atlas.TensorCategories.code.ModuleCategory.Theorem2116
import Atlas.TensorCategories.code.ModuleCategory
import Atlas.TensorCategories.code.ModuleCategoryDecomp
import Atlas.TensorCategories.code.ModuleCategoryEquiv

import Atlas.TensorCategories.code.ModuleFunctor
import Atlas.TensorCategories.code.ModuleFunctorAbelianDefs

import Atlas.TensorCategories.code.ModuleFunctorDefs

import Atlas.TensorCategories.code.ModuleOverAlgebra
import Atlas.TensorCategories.code.ModuleRigidityCompat
-- import Formalization.MonoidalCategoryDef  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.MonoidalFunctorDef
import Atlas.TensorCategories.code.MonoidalFunctorProps
import Atlas.TensorCategories.code.MonoidalFunctorsCohomology
import Atlas.TensorCategories.code.MonoidalStructuresGraded
-- import Formalization.MonoidalUnitProperties  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.MoritaEquivalence
-- import Formalization.MultifusionSemisimple  -- commented out: conflicts with other imports
-- import Formalization.NicholsZoeller  -- commented out: conflicts with other imports

import Mathlib.Data.Matrix.Basic
import Atlas.TensorCategories.code.PerronFrobenius.SimplexFixedPoint

import Atlas.TensorCategories.code.PerronFrobeniusProof
import Atlas.TensorCategories.code.PivotalSpherical

import Atlas.TensorCategories.code.PointedTensorCategory
import Atlas.TensorCategories.code.ProjectiveCoverInfra
-- import Formalization.ProjectiveUnitSemisimple  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.Prop_1_45_10
import Atlas.TensorCategories.code.Proposition_1_15_5
import Atlas.TensorCategories.code.Proposition_1_27_1
import Atlas.TensorCategories.code.Proposition_1_2_4

-- import Formalization.Proposition_1_36_4  -- commented out: conflicts with other imports
-- import Formalization.Proposition_1_36_5  -- commented out: conflicts with other imports
-- import Formalization.Proposition_1_42_9  -- commented out: conflicts with other imports
-- import Formalization.Proposition_1_43_4  -- commented out: conflicts with other imports

import Atlas.TensorCategories.code.Proposition_1_45_2
import Atlas.TensorCategories.code.Proposition_1_45_5
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite

-- import Formalization.Proposition_1_52_5  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.Proposition_1_6_4
import Atlas.TensorCategories.code.Proposition_2_10_7
import Atlas.TensorCategories.code.Proposition_2_12_2

import Atlas.TensorCategories.code.Proposition_2_1_3

import Atlas.TensorCategories.code.QBinomial
import Atlas.TensorCategories.code.QuantumGroupGeneral
-- import Formalization.QuantumGroups  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.QuantumSl2
import Atlas.TensorCategories.code.QuantumSl2Concrete
import Atlas.TensorCategories.code.QuantumSl2Instance

-- import Formalization.QuasiBialgebra  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.QuasiTensorFunctor
import Atlas.TensorCategories.code.QuasiTensorFunctorProjective
import Atlas.TensorCategories.code.ReductiveGroup
import Atlas.TensorCategories.code.RegularElement
import Atlas.TensorCategories.code.RegularObject
import Atlas.TensorCategories.code.RegularObjectAbsorption
import Atlas.TensorCategories.code.RigidAbelianDecomp
import Atlas.TensorCategories.code.RigidMonoidalDuality
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Simple
-- import Formalization.Sec1_31_38_Props  -- commented out: conflicts with other imports

import Atlas.TensorCategories.code.SemisimpleMultitensor

import Atlas.TensorCategories.code.SkewPrimitive
-- import Formalization.SkewPrimitiveCategorical  -- commented out: conflicts with other imports
import Mathlib.Order.Filter.Basic
-- import Formalization.StarAlgebra  -- commented out: conflicts with other imports
-- import Formalization.StarAlgebraCorollaries  -- commented out: conflicts with other imports
-- import Formalization.StarAlgebras  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.SubquotientRelation
import Atlas.TensorCategories.code.SurjectiveFunctor
import Atlas.TensorCategories.code.SurjectiveTensorFunctor
-- import Formalization.SweedlerConcrete  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.SweedlerHopfInstance
-- import Formalization.TaftConcrete  -- commented out: conflicts with other imports
-- import Formalization.TaftHopfDataInstance  -- commented out: conflicts with other imports
-- import Formalization.TaftHopfInstance  -- commented out: conflicts with other imports

-- import Formalization.TannakaBialgebra  -- commented out: conflicts with other imports
-- import Formalization.TannakaHopfReconstruction  -- commented out: conflicts with other imports
-- import Formalization.TannakaReconstruction  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.TensorCategoryDef
import Atlas.TensorCategories.code.TensorDualAdj
import Atlas.TensorCategories.code.TensorExact
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

-- import Formalization.TensorImageLight  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.TensorNondegen.DualZero
import Atlas.TensorCategories.code.TensorNondegen.EvalCoevalArg
import Atlas.TensorCategories.code.TensorNondegen.ZeroTensorZero
import Atlas.TensorCategories.code.TensorNondegenInstance

import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Atlas.TensorCategories.code.TensorProjective.Proposition_1_13_6
import Atlas.TensorCategories.code.TensorProjective.TensorSummand
import Atlas.TensorCategories.code.Theorem_1_15_8
-- import Formalization.Theorem_1_21_3  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_22_11  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_23_1  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_23_2  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.Theorem_1_25_2
-- import Formalization.Theorem_1_34_8  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_35_6  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_50_1  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_53_1  -- commented out: conflicts with other imports
-- import Formalization.Theorem_2_11_2  -- commented out: conflicts with other imports

import Atlas.TensorCategories.code.TraceNonzero
-- import Formalization.TwistEquivMonoidal  -- commented out: conflicts with other imports
-- import Formalization.Twists  -- commented out: conflicts with other imports

-- import Formalization.UnitProjective  -- commented out: conflicts with other imports
import Atlas.TensorCategories.code.UnitProjectiveSemisimple

import Atlas.TensorCategories.code.UnitSemisimplicity.EvalCoeval
import Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact
import Atlas.TensorCategories.code.UnitSemisimplicity.TensorExactness
import Atlas.TensorCategories.code.UnitSemisimplicity.UnitSimple

import Atlas.TensorCategories.code.VecCategoricalFusionData
import Atlas.TensorCategories.code.VecDualMapBridge
import Atlas.TensorCategories.code.VecInstances
import Atlas.TensorCategories.code.VecPivotal.DoubleDualIso
import Atlas.TensorCategories.code.VecPivotal.MonoidalCoherence

import Atlas.TensorCategories.code.VecPivotal.SphericalInstance
import Atlas.TensorCategories.code.VecPivotal
import Atlas.TensorCategories.code.VecPivotalConcrete

import Atlas.TensorCategories.code.VecSemisimple
import Atlas.TensorCategories.code.VecSphericalConcrete
import Atlas.TensorCategories.code.VecTensorDualCoherence
import Atlas.TensorCategories.code.ZPlusModules
