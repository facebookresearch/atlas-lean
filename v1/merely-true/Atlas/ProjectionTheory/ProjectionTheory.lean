/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.ABCSumProduct
import Atlas.ProjectionTheory.code.AuxiliaryLemma
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib
import Atlas.ProjectionTheory.code.BKTLemma2
import Atlas.ProjectionTheory.code.BKTLemma3

import Atlas.ProjectionTheory.code.BKTProposition

import Atlas.ProjectionTheory.code.BSGProposition
import Mathlib.Combinatorics.Additive.Energy

import Atlas.ProjectionTheory.code.BalogSzemerediGowers
import Atlas.ProjectionTheory.code.BandlimitedBound

import Atlas.ProjectionTheory.code.BeckTheorem
import Atlas.ProjectionTheory.code.BombieriVinogradov
import Atlas.ProjectionTheory.code.BorsukUlam
import Atlas.ProjectionTheory.code.BourgainCorollary
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Atlas.ProjectionTheory.code.BourgainLemma
import Atlas.ProjectionTheory.code.BourgainLemma2
import Atlas.ProjectionTheory.code.BourgainProjection
import Atlas.ProjectionTheory.code.BourgainProjectionRestated

import Atlas.ProjectionTheory.code.CellDecomposition
import Atlas.ProjectionTheory.code.ContagiousStructure
import Atlas.ProjectionTheory.code.ContinuumBeck
import Atlas.ProjectionTheory.code.DeltaRegular
import Atlas.ProjectionTheory.code.DilatedSumsetExpansion
import Atlas.ProjectionTheory.code.DirichletPrimesAP
import Atlas.ProjectionTheory.code.DoubleCountingFF
import Atlas.ProjectionTheory.code.DoubleCountingLower
import Atlas.ProjectionTheory.code.DoubleCountingReal
import Atlas.ProjectionTheory.code.DoubleCountingRealCor
import Atlas.ProjectionTheory.code.DoubleCountingSimple
import Atlas.ProjectionTheory.code.EpsilonBadPairs
import Atlas.ProjectionTheory.code.EpsilonImprovement

import Atlas.ProjectionTheory.code.EuclideanProjectionBound
import Atlas.ProjectionTheory.code.FareySeparation
import Atlas.ProjectionTheory.code.FiniteFieldProjection
import Atlas.ProjectionTheory.code.FourierAffinePlane
import Atlas.ProjectionTheory.code.FourierBoundFF
import Atlas.ProjectionTheory.code.FourierBoundReal
import Atlas.ProjectionTheory.code.FourierFF
import Atlas.ProjectionTheory.code.FourierProjectionDictionary
import Atlas.ProjectionTheory.code.FourierProjectionDiscrete
import Atlas.ProjectionTheory.code.FourierProjectionSubspace
import Atlas.ProjectionTheory.code.FreimanRuzsa

import Atlas.ProjectionTheory.code.FurstenbergCorollary
import Atlas.ProjectionTheory.code.FurstenbergProposition
import Atlas.ProjectionTheory.code.GGGHMW
import Atlas.ProjectionTheory.code.GSW
import Atlas.ProjectionTheory.code.GridProjectionBound
import Atlas.ProjectionTheory.code.HamSandwich
import Atlas.ProjectionTheory.code.HamSandwichFinite
import Atlas.ProjectionTheory.code.HausdorffSpacing
import Atlas.ProjectionTheory.code.HighFreqMultConv

import Atlas.ProjectionTheory.code.KeyLemmaBSG
import Atlas.ProjectionTheory.code.L2BoundLineSum
import Atlas.ProjectionTheory.code.L2MixingSigma1
import Atlas.ProjectionTheory.code.LMWY
import Atlas.ProjectionTheory.code.LargeSieveAvg
import Atlas.ProjectionTheory.code.LargeSieveCorollary
import Atlas.ProjectionTheory.code.LargeSieveMultConv
import Atlas.ProjectionTheory.code.LargeSieveSize

import Atlas.ProjectionTheory.code.LinnikLargeSieve

import Atlas.ProjectionTheory.code.MainLemma2F
import Atlas.ProjectionTheory.code.MainLemma2R
import Atlas.ProjectionTheory.code.MainLemmaFF
import Atlas.ProjectionTheory.code.MainLemmaReal
import Atlas.ProjectionTheory.code.Marstrand

import Atlas.ProjectionTheory.code.MultConvLinftyBound
import Atlas.ProjectionTheory.code.MultConvProjection
import Atlas.ProjectionTheory.code.MultiplicativeConvolution

import Atlas.ProjectionTheory.code.OSRW
import Atlas.ProjectionTheory.code.OSRWSharp
import Atlas.ProjectionTheory.code.Oppenheim

import Atlas.ProjectionTheory.code.OrthogonalityLines
import Atlas.ProjectionTheory.code.OrthogonalityTubes
import Atlas.ProjectionTheory.code.ParsevalFF
import Atlas.ProjectionTheory.code.ParsevalHighFreq
import Atlas.ProjectionTheory.code.Plunnecke

import Atlas.ProjectionTheory.code.PolyK

import Atlas.ProjectionTheory.code.PolynomialHamSandwich
import Atlas.ProjectionTheory.code.ProjectionIncidence
import Atlas.ProjectionTheory.code.ProjectionSmoothing
import Atlas.ProjectionTheory.code.ProjectivePair
import Atlas.ProjectionTheory.code.RuzsaTriangle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Card
import Atlas.ProjectionTheory.code.SelbergExpansion
import Atlas.ProjectionTheory.code.SelbergSpectralGap
import Atlas.ProjectionTheory.code.SiegelWalfisz
import Atlas.ProjectionTheory.code.SieveTheorem1S
import Atlas.ProjectionTheory.code.Submultiplicative

import Atlas.ProjectionTheory.code.SzemerediTrotter
import Atlas.ProjectionTheory.code.SzemerediTrotterProjection

import Atlas.ProjectionTheory.code.TwoEnds
import Atlas.ProjectionTheory.code.UniformSet
import Atlas.ProjectionTheory.code.Uniformization
