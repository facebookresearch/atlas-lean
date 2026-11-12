/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Atlas.AnAlgorithmistsToolkit.code.PolarBody
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Basic
import Mathlib.Topology.Defs.Basic

open Set
open scoped Pointwise

namespace ConvexGeometry

def IsConvexBody {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (C : Set E) : Prop :=
  Convex ℝ C ∧ IsCompact C ∧ (interior C).Nonempty

theorem IsConvexBody.convex {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {C : Set E} (h : IsConvexBody C) : Convex ℝ C :=
  h.1

theorem IsConvexBody.isCompact {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {C : Set E} (h : IsConvexBody C) : IsCompact C :=
  h.2.1

theorem IsConvexBody.interior_nonempty {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E]
    {C : Set E} (h : IsConvexBody C) : (interior C).Nonempty :=
  h.2.2

noncomputable abbrev minkowskiFunctional {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : Set E) (x : E) : ℝ :=
  gauge C x

open Pointwise in
def banachMazurAdmissible {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K L : Set E) : Set ℝ :=
  {d : ℝ | 0 < d ∧ ∃ T : E ≃ₗ[ℝ] E, T '' L ⊆ K ∧ K ⊆ d • (T '' L)}

noncomputable def banachMazurDist {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K L : Set E) : ℝ :=
  sInf (banachMazurAdmissible K L)

section JohnEllipsoid

open MeasureTheory

variable {n : ℕ}

def IsEllipsoid (E : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
    E = T '' Metric.closedBall 0 1

def IsOriginSymmetric (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x, x ∈ K ↔ -x ∈ K

def unitBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall 0 1

def IsMaxVolInscribedEllipsoid (E K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsEllipsoid E ∧ E ⊆ K ∧
    ∀ E' : Set (EuclideanSpace ℝ (Fin n)),
      IsEllipsoid E' → E' ⊆ K → volume E' ≤ volume E

def JohnConditions (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  unitBall n ⊆ K ∧
  ∃ (m : ℕ) (u : Fin m → EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ),
    (∀ i, ‖u i‖ = 1) ∧
    (∀ i, u i ∈ frontier K) ∧
    (∀ i, 0 < c i) ∧
    (∑ i, c i • u i = 0) ∧
    (∀ x : EuclideanSpace ℝ (Fin n),
      ∑ i, c i * (@inner ℝ _ _ x (u i)) ^ 2 = ‖x‖ ^ 2)




end JohnEllipsoid

theorem separating_hyperplane {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {K : Set E} {p : E}
    (hK : IsConvexBody K) (hp : p ∉ K) :
    ∃ (f : E →L[ℝ] ℝ) (u : ℝ), (∀ a ∈ K, f a < u) ∧ u < f p := by
  have hclosed : IsClosed K := hK.isCompact.isClosed
  have hconvex : Convex ℝ K := hK.convex
  obtain ⟨f, u, hlt, hgt⟩ := geometric_hahn_banach_closed_point hconvex hclosed hp
  exact ⟨f, u, hlt, hgt⟩



def halfspacePolytope {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} (a : ι → E) : Set E :=
  { x : E | ∀ i, @inner ℝ E _ (a i) x ≤ 1 }


section ConeReplacementLemma

open MeasureTheory

noncomputable def volumeRatio {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (K L : Set α) : ENNReal :=
  μ (K ∩ L) / μ K

def posHalfSpace (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | 0 ≤ x 0}

def IsConeAligned {n : ℕ} (C : Set (Fin (n + 1) → ℝ)) : Prop :=
  ∃ (y : Fin (n + 1) → ℝ), 0 < y 0 ∧
    (∀ i : Fin (n + 1), i ≠ 0 → y i = 0) ∧
    (∃ Hpos Hneg : ℝ, 0 < Hpos ∧ 0 ≤ Hneg ∧ ∀ x ∈ C, -Hneg ≤ x 0 ∧ x 0 ≤ Hpos) ∧
    (∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (y + t • (x - y)) ∈ C)



end ConeReplacementLemma

end ConvexGeometry
