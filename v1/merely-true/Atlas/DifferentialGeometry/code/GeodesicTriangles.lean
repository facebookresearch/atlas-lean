/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Atlas.DifferentialGeometry.code.Geodesics

open scoped InnerProductSpace
open EuclideanGeometry

noncomputable section

namespace Geodesics

structure IsMetricGeodesicSegment {X : Type*} [MetricSpace X] (γ : ℝ → X)
    (p q : X) : Prop where
  source : γ 0 = p
  target : γ 1 = q
  proportional : ∀ s t : ℝ, s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
    dist (γ s) (γ t) = |t - s| * dist p q

structure GeodesicTriangle (X : Type*) [MetricSpace X] where
  p₁ : X
  p₂ : X
  p₃ : X
  γ₁₂ : ℝ → X
  γ₂₃ : ℝ → X
  γ₁₃ : ℝ → X
  isGeodesic₁₂ : IsMetricGeodesicSegment γ₁₂ p₁ p₂
  isGeodesic₂₃ : IsMetricGeodesicSegment γ₂₃ p₂ p₃
  isGeodesic₁₃ : IsMetricGeodesicSegment γ₁₃ p₁ p₃

def GeodesicTriangle.sideA {X : Type*} [MetricSpace X] (T : GeodesicTriangle X) : ℝ :=
  dist T.p₂ T.p₃

def GeodesicTriangle.sideB {X : Type*} [MetricSpace X] (T : GeodesicTriangle X) : ℝ :=
  dist T.p₁ T.p₃

def GeodesicTriangle.sideC {X : Type*} [MetricSpace X] (T : GeodesicTriangle X) : ℝ :=
  dist T.p₁ T.p₂

def comparisonAngle {X : Type*} [MetricSpace X] (p₁ p₂ p₃ : X) : ℝ :=
  let a := dist p₂ p₃
  let b := dist p₁ p₃
  let c := dist p₁ p₂
  if b = 0 ∨ c = 0 then 0
  else Real.arccos ((b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c))

def GeodesicTriangle.comparisonAngleAt₁ {X : Type*} [MetricSpace X]
    (T : GeodesicTriangle X) : ℝ :=
  comparisonAngle T.p₁ T.p₂ T.p₃

def GeodesicTriangle.comparisonAngleAt₂ {X : Type*} [MetricSpace X]
    (T : GeodesicTriangle X) : ℝ :=
  comparisonAngle T.p₂ T.p₁ T.p₃

def GeodesicTriangle.comparisonAngleAt₃ {X : Type*} [MetricSpace X]
    (T : GeodesicTriangle X) : ℝ :=
  comparisonAngle T.p₃ T.p₁ T.p₂

structure ComparisonTriangle (X : Type*) [MetricSpace X] (T : GeodesicTriangle X) where
  q₁ : EuclideanSpace ℝ (Fin 2)
  q₂ : EuclideanSpace ℝ (Fin 2)
  q₃ : EuclideanSpace ℝ (Fin 2)
  dist_eq₁₂ : dist q₁ q₂ = dist T.p₁ T.p₂
  dist_eq₂₃ : dist q₂ q₃ = dist T.p₂ T.p₃
  dist_eq₁₃ : dist q₁ q₃ = dist T.p₁ T.p₃

end Geodesics
