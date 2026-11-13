/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.AffineCoxeterHypProof
import Atlas.Buildings.code.AffineCoxeter.AffineCriterion
import Atlas.Buildings.code.AffineCoxeter.AffineWeylBook
import Atlas.Buildings.code.AffineCoxeter.CanonicalMetric

import Atlas.Buildings.code.AffineCoxeter.Faces
import Atlas.Buildings.code.AffineCoxeter.FiniteProperParabolicsInstance
import Atlas.Buildings.code.AffineCoxeter.GeometricRealization
import Atlas.Buildings.code.AffineCoxeter.LatticeFiniteness
import Atlas.Buildings.code.AffineCoxeter.LocalFiniteness
import Atlas.Buildings.code.AffineCoxeter.PerronFrobeniusCorollary
import Atlas.Buildings.code.AffineCoxeter.PerronFrobeniusProof
import Atlas.Buildings.code.AffineCoxeter.SemidirectProduct
import Atlas.Buildings.code.AffineCoxeter.SphericalFiniteInstance
import Atlas.Buildings.code.AffineCoxeter.TitsCone
import Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity
import Atlas.Buildings.code.AffineCoxeter.TitsConeCorollary
import Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic
import Atlas.Buildings.code.AffineCoxeter.TitsConeInterior

import Atlas.Buildings.code.AffineCoxeter.TransitiveAlcovesHelper
import Atlas.Buildings.code.BNPair.Basic
import Atlas.Buildings.code.BNPair.BruhatPropertiesInstance
import Atlas.Buildings.code.BNPair.BruhatPropertiesWiring
import Atlas.Buildings.code.BNPair.BuildingAxiomsFromBNPairs
import Atlas.Buildings.code.BNPair.BuildingsFromBNPairs
import Atlas.Buildings.code.BNPair.CellCoverProof
import Atlas.Buildings.code.BNPair.CellDisjointHelpers
import Atlas.Buildings.code.BNPair.CellDisjointProof
import Atlas.Buildings.code.BNPair.CellInvProof
import Atlas.Buildings.code.BNPair.CellMulFiniteProof
import Atlas.Buildings.code.BNPair.CellMulParabolicProof
import Atlas.Buildings.code.BNPair.ConjugatorProof
import Atlas.Buildings.code.BNPair.DoubleCosets
import Atlas.Buildings.code.BNPair.FromBuilding
import Atlas.Buildings.code.BNPair.FurtherBruhatTits
import Atlas.Buildings.code.BNPair.Generalized.Defs
import Atlas.Buildings.code.BNPair.Generalized.Theorems
import Atlas.Buildings.code.BNPair.Generalized.TypePreserving

import Atlas.Buildings.code.BNPair.NormalizerParabolicProof
import Atlas.Buildings.code.BNPair.ParabolicDefs
import Atlas.Buildings.code.BNPair.Parabolics

import Atlas.Buildings.code.BNPair.PropositionParabolics
import Atlas.Buildings.code.BNPair.SphericalCase
import Atlas.Buildings.code.BNPair.SubgroupOverBProof
import Atlas.Buildings.code.BNPair.TKernel
import Atlas.Buildings.code.Building.Affine
import Atlas.Buildings.code.Building.AffineCurvature
import Atlas.Buildings.code.Building.AffineIsometry.Contexts
import Atlas.Buildings.code.Building.AffineIsometry.LatticeChains
import Atlas.Buildings.code.Building.AffineIsometry.Theorems

import Atlas.Buildings.code.Building.AffineIsometryAxiomsAction
import Atlas.Buildings.code.Building.AffineIsometryGroups.GroupAction
import Atlas.Buildings.code.Building.AffineIsometryGroups.StrongTransitivity

import Atlas.Buildings.code.Building.AffineMetric
import Atlas.Buildings.code.Building.AffineMetricGR
import Atlas.Buildings.code.Building.AffineSLV
import Atlas.Buildings.code.Building.AffineSLVStrong
import Atlas.Buildings.code.Building.AffineSLVWellDef
import Atlas.Buildings.code.Building.ApartmentsCoxeter
import Atlas.Buildings.code.Building.ApplicationsToGroups

import Atlas.Buildings.code.Building.AptFoldingFromRetraction
import Atlas.Buildings.code.Building.AptIsCoxeterProof

import Atlas.Buildings.code.Building.AptThinness
import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.Building.BornologyGroups
import Atlas.Buildings.code.Building.BornologyProposition
import Atlas.Buildings.code.Building.BruhatTitsFixedPoint
import Atlas.Buildings.code.Building.ChamberCompactClosure
import Atlas.Buildings.code.Building.CombinatorialGeometry.GateConvex
import Atlas.Buildings.code.Building.CombinatorialGeometry.PrescribedGallery
import Atlas.Buildings.code.Building.CombinatorialGeometry.PropStrongIsoCombinatorial
import Atlas.Buildings.code.Building.CombinatorialGeometry.RetractionHalfApartments

import Atlas.Buildings.code.Building.CombinatorialGeometry.ThreeChamber

import Atlas.Buildings.code.Building.CompactSubgroups
import Atlas.Buildings.code.Building.Convexity
import Atlas.Buildings.code.Building.CoxeterComplexFoldings
import Atlas.Buildings.code.Building.DiagBlockEmbed
import Atlas.Buildings.code.Building.DiscreteFibers
import Atlas.Buildings.code.Building.FixedPointSubgroups
import Atlas.Buildings.code.Building.GalleryProjectionHelper
import Atlas.Buildings.code.Building.GoodMaximalBounded
import Atlas.Buildings.code.Building.GroupApplicationsCh17
import Atlas.Buildings.code.Building.Infinity.AffineFunc
import Atlas.Buildings.code.Building.Infinity.ChamberSectorConfig
import Atlas.Buildings.code.Building.Infinity.CorSectorParallelism
import Atlas.Buildings.code.Building.Infinity.SectorGallery
import Atlas.Buildings.code.Building.Infinity.SectorParallelism
import Atlas.Buildings.code.Building.Infinity.Sectors
import Atlas.Buildings.code.Building.Infinity.SimplexAtInfinity

import Atlas.Buildings.code.Building.InfinityConstruction
import Atlas.Buildings.code.Building.InfinityMaps

import Atlas.Buildings.code.Building.IwahoriGLn
import Atlas.Buildings.code.Building.IwahoriGLnBaseCase
import Atlas.Buildings.code.Building.IwahoriGLnClearing
import Atlas.Buildings.code.Building.IwahoriGLnDefs
import Atlas.Buildings.code.Building.IwahoriGLnExistence
import Atlas.Buildings.code.Building.IwahoriGLnHelpers
import Atlas.Buildings.code.Building.IwahoriGLnUniqueness
import Atlas.Buildings.code.Building.LabelPreservingIso
import Atlas.Buildings.code.Building.Labels
import Atlas.Buildings.code.Building.Link
import Atlas.Buildings.code.Building.LinkAdjacencyLifting
import Atlas.Buildings.code.Building.LinkBuilding
import Atlas.Buildings.code.Building.LinkBuildingIsoHelper
import Atlas.Buildings.code.Building.LinkCoxeterHelper
import Atlas.Buildings.code.Building.MaximalApartments

import Atlas.Buildings.code.Building.OppositeChambers
import Atlas.Buildings.code.Building.PropositionRetractionProperties

import Atlas.Buildings.code.Building.RetractionDef
import Atlas.Buildings.code.Building.RetractionOntoApartment
import Atlas.Buildings.code.Building.RetractionProperties
import Atlas.Buildings.code.Building.Spherical
import Atlas.Buildings.code.Building.SphericalFiniteDiameter
import Atlas.Buildings.code.Building.StrongIsoExtHelper
import Atlas.Buildings.code.Building.StrongIsometryExt
import Atlas.Buildings.code.Building.StrongIsometryExtMain

import Atlas.Buildings.code.Building.ThicknessAptStructureProof
import Atlas.Buildings.code.Building.ThicknessFoldings

import Atlas.Buildings.code.Building.TitsExchangeFromFoldings

import Atlas.Buildings.code.Building.TitsTheoremProof
import Atlas.Buildings.code.Building.UniqueLabellingHelper
import Atlas.Buildings.code.Building.UniqueRetraction
import Atlas.Buildings.code.Building.VertexActionHelper
import Atlas.Buildings.code.Building.WallReflectionAction

import Atlas.Buildings.code.ChamberComplex.Basic
import Atlas.Buildings.code.ChamberComplex.CoxeterComplex
import Atlas.Buildings.code.ChamberComplex.Folding
import Atlas.Buildings.code.ChamberComplex.FoldingCorollaries
import Atlas.Buildings.code.ChamberComplex.GalleryConcatenation
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterFolding
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterFoldingHelpers
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterProperties
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.IsCoxeterCharacterized
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.ThinFolding
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.TitsForwardHelpers
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.WallCrossing

import Atlas.Buildings.code.ChamberComplex.Uniqueness
import Atlas.Buildings.code.ChamberComplex.UniquenessBook
import Atlas.Buildings.code.CoxeterGroup.Basic
import Atlas.Buildings.code.CoxeterGroup.BraidRelation
import Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.Assembly
import Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.DihedralHelpers

import Atlas.Buildings.code.CoxeterGroup.BruhatChainUnconditional
import Atlas.Buildings.code.CoxeterGroup.BruhatOrder

import Atlas.Buildings.code.CoxeterGroup.BruhatSubexpression
import Atlas.Buildings.code.CoxeterGroup.CoxeterHomomorphism
import Atlas.Buildings.code.CoxeterGroup.CoxeterSystemFromDeletion
import Atlas.Buildings.code.CoxeterGroup.CyclicRotation
import Atlas.Buildings.code.CoxeterGroup.DeletionCondition
import Atlas.Buildings.code.CoxeterGroup.DeletionInjectivity
import Atlas.Buildings.code.CoxeterGroup.DeletionInjectivityHelpers
import Atlas.Buildings.code.CoxeterGroup.DeletionWordRelation
import Atlas.Buildings.code.CoxeterGroup.DescentInversionBridge
import Atlas.Buildings.code.CoxeterGroup.DihedralLengthBound
import Atlas.Buildings.code.CoxeterGroup.DihedralPositivity
import Atlas.Buildings.code.CoxeterGroup.DihedralPositivityFinite
import Atlas.Buildings.code.CoxeterGroup.DihedralWordPositivity
import Atlas.Buildings.code.CoxeterGroup.ExchangeConditionGenuine
import Atlas.Buildings.code.CoxeterGroup.ExchangeConditionProof
import Atlas.Buildings.code.CoxeterGroup.ExchangeConditionWiring
import Atlas.Buildings.code.CoxeterGroup.ExchangeDeletion
import Mathlib.GroupTheory.Coxeter.Inversion
import Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation
import Atlas.Buildings.code.CoxeterGroup.InversionMultiplication
import Atlas.Buildings.code.CoxeterGroup.InversionSet
import Mathlib.GroupTheory.Coxeter.Length

import Atlas.Buildings.code.CoxeterGroup.ListAlternating

import Atlas.Buildings.code.CoxeterGroup.OrderAxiom
import Atlas.Buildings.code.CoxeterGroup.ParabolicDecomp
import Atlas.Buildings.code.CoxeterGroup.ParabolicInjective
import Atlas.Buildings.code.CoxeterGroup.ParabolicPositivity
import Atlas.Buildings.code.CoxeterGroup.ParabolicSubgroups
import Atlas.Buildings.code.CoxeterGroup.ParitySign
import Atlas.Buildings.code.CoxeterGroup.PosOfAscentProof
import Atlas.Buildings.code.CoxeterGroup.ReflectionIdentificationGenuine

import Atlas.Buildings.code.CoxeterGroup.ReflectionLengthDecrease
import Atlas.Buildings.code.CoxeterGroup.Reflections
import Atlas.Buildings.code.CoxeterGroup.RootConjugacy
import Atlas.Buildings.code.CoxeterGroup.RootReflectionLemmas
import Atlas.Buildings.code.CoxeterGroup.RootSignChangeProof
import Atlas.Buildings.code.CoxeterGroup.RootSystem
import Atlas.Buildings.code.CoxeterGroup.Roots
import Atlas.Buildings.code.CoxeterGroup.SevenFamilies
import Atlas.Buildings.code.CoxeterGroup.SigmaOrder
import Atlas.Buildings.code.CoxeterGroup.SignChangeExchangeFinal

import Atlas.Buildings.code.CoxeterGroup.SignedPermGroup
import Atlas.Buildings.code.CoxeterGroup.SimpleReflectionInversions
import Atlas.Buildings.code.CoxeterGroup.StrongExchangeBridge
import Atlas.Buildings.code.CoxeterGroup.StrongExchangeProof
import Atlas.Buildings.code.CoxeterGroup.StrongExchangeUnconditional
import Atlas.Buildings.code.CoxeterGroup.SupportWellDefined
import Atlas.Buildings.code.CoxeterGroup.TypeABridge
import Atlas.Buildings.code.CoxeterGroup.TypeACoxeterSystem
import Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
import Atlas.Buildings.code.CoxeterGroup.TypeAIsomorphism
import Atlas.Buildings.code.CoxeterGroup.TypeCInjectivityHelper
import Atlas.Buildings.code.CoxeterGroup.UnconditionalExchange
import Atlas.Buildings.code.CoxeterGroup.UnluckyCase
import Atlas.Buildings.code.CoxeterGroup.WordSigmaInvariance
import Atlas.Buildings.code.CoxeterGroup.Words
import Atlas.Buildings.code.GeometricAlgebra.AnisotropicDecomposition
import Atlas.Buildings.code.GeometricAlgebra.AnisotropicHyperbolicTrivial

import Atlas.Buildings.code.GeometricAlgebra.BilinFormComplementation
import Atlas.Buildings.code.GeometricAlgebra.BilinHermitianProps
import Atlas.Buildings.code.GeometricAlgebra.BilinearForms
import Atlas.Buildings.code.GeometricAlgebra.CoordinateExamples
import Atlas.Buildings.code.GeometricAlgebra.CorBilinearHermitianForms
import Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Atlas.Buildings.code.GeometricAlgebra.FinrankOrthogonal
import Atlas.Buildings.code.GeometricAlgebra.FlagEquivalenceInstance
import Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics
import Atlas.Buildings.code.GeometricAlgebra.HyperbolicCancellation
import Atlas.Buildings.code.GeometricAlgebra.IsometryDet

import Atlas.Buildings.code.GeometricAlgebra.IsotropicFlagsParabolics
import Mathlib
import Atlas.Buildings.code.GeometricAlgebra.KernelDecomposition
import Atlas.Buildings.code.GeometricAlgebra.LagrangianDimBound
import Atlas.Buildings.code.GeometricAlgebra.LagrangianFinrank
import Atlas.Buildings.code.GeometricAlgebra.LagrangianHardProof
import Atlas.Buildings.code.GeometricAlgebra.MaximalIsotropicHelper
import Atlas.Buildings.code.GeometricAlgebra.NondegenerateThreeWay
import Atlas.Buildings.code.GeometricAlgebra.OppositeConjugacyComposition
import Atlas.Buildings.code.GeometricAlgebra.OppositeConjugacyInstance
import Atlas.Buildings.code.GeometricAlgebra.OppositeConjugacyProof
import Atlas.Buildings.code.GeometricAlgebra.SemidirectExistence
import Atlas.Buildings.code.GeometricAlgebra.SemidirectExistenceInstance

import Atlas.Buildings.code.GeometricAlgebra.WittCancellationDirectSum
import Atlas.Buildings.code.GeometricAlgebra.WittCancellationIndependent
import Atlas.Buildings.code.GeometricAlgebra.WittExtensionProof
import Atlas.Buildings.code.GeometricAlgebra.WittTheorem
import Atlas.Buildings.code.HeckeAlgebra.Generalized
import Atlas.Buildings.code.HeckeAlgebra.Generic
import Atlas.Buildings.code.HeckeAlgebra.GenericAlgebraUniqueness
import Atlas.Buildings.code.HeckeAlgebra.HeckeStructureTheorem
import Atlas.Buildings.code.HeckeAlgebra.OperatorCommutativity
import Atlas.Buildings.code.HeckeAlgebra.Section6_1_Theorem
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.InnerProductSpace.Basic
import Atlas.Buildings.code.IsometryExtensionLemma
import Atlas.Buildings.code.Reflection.AffineReflectionProposition
import Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
import Atlas.Buildings.code.Reflection.AffineWeylGroups
import Atlas.Buildings.code.Reflection.AffineWeylProposition12_5
import Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv

import Atlas.Buildings.code.Reflection.DihedralRootHelpers
import Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Defs
import Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Theorems

import Atlas.Buildings.code.Reflection.GenericFunctional
import Atlas.Buildings.code.Reflection.HyperplaneChambers
import Atlas.Buildings.code.Reflection.InnerProductWalls

import Atlas.Buildings.code.Reflection.ReflectionGroupsCoxeter
import Atlas.Buildings.code.Reflection.UniqueAdjacentChamber
import Atlas.Buildings.code.Reflection.WallSeparation

import Atlas.Buildings.code.SphericalBuilding.AdaptedBasisProof
import Atlas.Buildings.code.SphericalBuilding.AdaptedBasisSingle
import Atlas.Buildings.code.SphericalBuilding.BasisExtensionChain
import Atlas.Buildings.code.SphericalBuilding.BasisFromFlagProof
import Atlas.Buildings.code.SphericalBuilding.FinsetGapCorrespondenceProof
import Atlas.Buildings.code.SphericalBuilding.GLn
import Atlas.Buildings.code.SphericalBuilding.GLnApartmentIsoUnconditional
import Atlas.Buildings.code.SphericalBuilding.GLnB0Cascade
import Atlas.Buildings.code.SphericalBuilding.GLnBaseFlag
import Atlas.Buildings.code.SphericalBuilding.GLnBuildingInstance
import Atlas.Buildings.code.SphericalBuilding.GLnChainRefinement
import Atlas.Buildings.code.SphericalBuilding.GLnCommonApartment
import Atlas.Buildings.code.SphericalBuilding.GLnCommonApartmentUnconditional
import Atlas.Buildings.code.SphericalBuilding.GLnFlagToFrame
import Atlas.Buildings.code.SphericalBuilding.GLnGapAnalysis
import Atlas.Buildings.code.SphericalBuilding.GLnInstance
import Atlas.Buildings.code.SphericalBuilding.GLnPanelExtension
import Atlas.Buildings.code.SphericalBuilding.GLnSimultaneousRefinement
import Atlas.Buildings.code.SphericalBuilding.GLnThinApartment
import Atlas.Buildings.code.SphericalBuilding.GLnThinApartmentUnconditional
import Atlas.Buildings.code.SphericalBuilding.IsometryApartmentExchange
import Atlas.Buildings.code.SphericalBuilding.IsometryBuildingInstance
import Atlas.Buildings.code.SphericalBuilding.IsometryBuildingWiring
import Atlas.Buildings.code.SphericalBuilding.IsometryCommonApartment
import Atlas.Buildings.code.SphericalBuilding.IsometryGroups
import Atlas.Buildings.code.SphericalBuilding.JordanHolderFrame
import Atlas.Buildings.code.SphericalBuilding.JordanHolderPermutation
import Atlas.Buildings.code.SphericalBuilding.LagrangianExtension
import Atlas.Buildings.code.SphericalBuilding.Oriflamme

import Atlas.Buildings.code.SphericalBuilding.RefinementCompatibility
import Atlas.Buildings.code.SphericalBuilding.RefinementDimJumps
import Atlas.Buildings.code.SphericalBuilding.RefinementFrame
import Atlas.Buildings.code.SphericalBuilding.SOActionLemma
import Atlas.Buildings.code.SphericalBuilding.SchreierRefinement
import Atlas.Buildings.code.SphericalBuilding.TwoChamberHypFinal
import Atlas.Buildings.code.Valuation.DVRInstances
import Atlas.Buildings.code.Valuation.DiscreteValuationBook
import Atlas.Buildings.code.Valuation.IwahoriDecomp
import Atlas.Buildings.code.Valuation.LatticesValuations
import Atlas.Buildings.code.Valuation.MaximalLattice
