/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.AbsoluteValues
import Atlas.ArithmeticGeometry.code.AdelePlusFDim
import Atlas.ArithmeticGeometry.code.AdeleQuotientDim
import Atlas.ArithmeticGeometry.code.AffineCurve
import Atlas.ArithmeticGeometry.code.AffineVarieties
import Atlas.ArithmeticGeometry.code.AlgebraicGeometryBasics

import Atlas.ArithmeticGeometry.code.BSDConjecture
import Atlas.ArithmeticGeometry.code.BoundedHeightFinite
import Atlas.ArithmeticGeometry.code.CanonicalDivisors
import Atlas.ArithmeticGeometry.code.ClassGroupRatFunc
import Atlas.ArithmeticGeometry.code.ClosedPointMorphism
import Mathlib
import Atlas.ArithmeticGeometry.code.CompleteVarieties
import Atlas.ArithmeticGeometry.code.CompletenessResidueK
import Atlas.ArithmeticGeometry.code.CompletenessValuationCriterion
import Atlas.ArithmeticGeometry.code.Conics
import Atlas.ArithmeticGeometry.code.CoordinateRingSingular

import Atlas.ArithmeticGeometry.code.Corollary_20_4
import Atlas.ArithmeticGeometry.code.CotangentLocal
import Atlas.ArithmeticGeometry.code.CurveMorphisms
import Atlas.ArithmeticGeometry.code.CurveTheory
import Atlas.ArithmeticGeometry.code.DedekindDomains
import Atlas.ArithmeticGeometry.code.DegreePullback
import Atlas.ArithmeticGeometry.code.DescentFiniteness
import Atlas.ArithmeticGeometry.code.DivisorLineRatio
import Atlas.ArithmeticGeometry.code.Divisors
import Atlas.ArithmeticGeometry.code.EffectiveDivisors
import Atlas.ArithmeticGeometry.code.EllipticCurves
import Atlas.ArithmeticGeometry.code.FaltingsTheorem
import Atlas.ArithmeticGeometry.code.FiniteFields
import Atlas.ArithmeticGeometry.code.FunctionFieldEquiv
import Atlas.ArithmeticGeometry.code.FunctionFieldGenerators
import Atlas.ArithmeticGeometry.code.GaloisCohomology
import Atlas.ArithmeticGeometry.code.GaloisPlaceHelper
import Atlas.ArithmeticGeometry.code.GeneratorsModM2
import Atlas.ArithmeticGeometry.code.GenusBaseExtension
import Atlas.ArithmeticGeometry.code.GenusOnePlaneCubic
import Atlas.ArithmeticGeometry.code.GenusZeroP1

import Atlas.ArithmeticGeometry.code.HasseMinkowski
import Atlas.ArithmeticGeometry.code.HasseMinkowskiHelpers
import Atlas.ArithmeticGeometry.code.HasseMinkowskiProof
import Atlas.ArithmeticGeometry.code.Heights
import Atlas.ArithmeticGeometry.code.HenselsLemma
import Atlas.ArithmeticGeometry.code.Hilbert2Adic
import Atlas.ArithmeticGeometry.code.Hilbert2AdicCore
import Atlas.ArithmeticGeometry.code.HilbertBilinear
import Atlas.ArithmeticGeometry.code.HilbertFormulaOdd
import Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions
import Atlas.ArithmeticGeometry.code.HilbertProductFormula
import Atlas.ArithmeticGeometry.code.HilbertSymbol
import Atlas.ArithmeticGeometry.code.HilbertSymbol2Adic
import Atlas.ArithmeticGeometry.code.IdealNorm
import Atlas.ArithmeticGeometry.code.IndependenceOfValuations
import Atlas.ArithmeticGeometry.code.IndexOfSpeciality
import Atlas.ArithmeticGeometry.code.Isogenies
import Atlas.ArithmeticGeometry.code.IsogenyKernelAut
import Atlas.ArithmeticGeometry.code.JInvariant
import Atlas.ArithmeticGeometry.code.JInvariantInK
import Atlas.ArithmeticGeometry.code.JInvariantTwist

import Atlas.ArithmeticGeometry.code.Lemma2112
import Atlas.ArithmeticGeometry.code.Lemma22_10
import Atlas.ArithmeticGeometry.code.Lemma22_13
import Atlas.ArithmeticGeometry.code.Lemma22_15
import Atlas.ArithmeticGeometry.code.Lemma2417
import Atlas.ArithmeticGeometry.code.MordellWeil

import Atlas.ArithmeticGeometry.code.Morphisms
import Atlas.ArithmeticGeometry.code.MorphismsCurves
import Atlas.ArithmeticGeometry.code.NewtonPolygon
import Atlas.ArithmeticGeometry.code.PadicCompletion
import Atlas.ArithmeticGeometry.code.PadicElliptic
import Atlas.ArithmeticGeometry.code.PadicField
import Atlas.ArithmeticGeometry.code.PadicNumbers
import Atlas.ArithmeticGeometry.code.PadicQpCompletion
import Atlas.ArithmeticGeometry.code.PicardGroup
import Atlas.ArithmeticGeometry.code.ProductFormula
import Atlas.ArithmeticGeometry.code.ProductVarieties
import Atlas.ArithmeticGeometry.code.ProjectiveComplete
import Atlas.ArithmeticGeometry.code.ProjectiveMorphisms
import Atlas.ArithmeticGeometry.code.ProjectiveSpaceInstance
import Atlas.ArithmeticGeometry.code.ProjectiveVarieties
import Atlas.ArithmeticGeometry.code.QuadraticForms
import Atlas.ArithmeticGeometry.code.QuadraticReciprocity
import Atlas.ArithmeticGeometry.code.RationalLineCriterion
import Atlas.ArithmeticGeometry.code.RegularFunctions
import Atlas.ArithmeticGeometry.code.RegularLocalRings
import Atlas.ArithmeticGeometry.code.RiemannRoch
import Atlas.ArithmeticGeometry.code.RiemannRochP1
import Atlas.ArithmeticGeometry.code.RiemannTheorem
import Atlas.ArithmeticGeometry.code.ScalingLemma

import Atlas.ArithmeticGeometry.code.SquareClassApprox
import Atlas.ArithmeticGeometry.code.TangentSpaces
import Atlas.ArithmeticGeometry.code.TateShafarevich
import Atlas.ArithmeticGeometry.code.TaylorExpansion
import Atlas.ArithmeticGeometry.code.TensorProductDomain
import Atlas.ArithmeticGeometry.code.Theorem11_1
import Atlas.ArithmeticGeometry.code.Theorem1324
import Atlas.ArithmeticGeometry.code.Theorem22_11
import Atlas.ArithmeticGeometry.code.Theorem22_14
import Atlas.ArithmeticGeometry.code.Theorem22_20
import Atlas.ArithmeticGeometry.code.TorsorIffJacobian

import Atlas.ArithmeticGeometry.code.Torsors
import Atlas.ArithmeticGeometry.code.TraceNorm
import Atlas.ArithmeticGeometry.code.Twists

import Atlas.ArithmeticGeometry.code.ValuationRings
import Atlas.ArithmeticGeometry.code.ValuedFields
import Atlas.ArithmeticGeometry.code.Varieties
import Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv

import Atlas.ArithmeticGeometry.code.WeakApproxFunctionFields
import Atlas.ArithmeticGeometry.code.WeakApproximation
import Atlas.ArithmeticGeometry.code.WeierstrassValBound
import Atlas.ArithmeticGeometry.code.WeilChatelet
