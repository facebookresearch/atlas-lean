/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Convex.Body
open MeasureTheory

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped NNReal

namespace HighDimensional

def IsCLipschitz {α : Type*} {β : Type*} [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
    (c : ℝ) (f : α → β) : Prop :=
  ∀ u v : α, ‖f u - f v‖ ≤ c * ‖u - v‖

structure IsDEmbedding {X : Type*} [MetricSpace X] [Fintype X] {k : ℕ}
    (D : ℝ) (f : X → EuclideanSpace ℝ (Fin k)) : Prop where
  one_lipschitz : ∀ x y : X, ‖f x - f y‖ ≤ dist x y
  distortion_bound : ∀ x y : X, dist x y ≤ D * ‖f x - f y‖


abbrev UnitSphere (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

instance (n : ℕ) : MeasurableSpace (UnitSphere n) := inferInstance

noncomputable def sphereMeasure (n : ℕ) : Measure (UnitSphere n) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

noncomputable def uniformSphereMeasure (n : ℕ) : Measure (UnitSphere n) :=
  (sphereMeasure n Set.univ)⁻¹ • sphereMeasure n

def IsMedian {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (M : ℝ) : Prop :=
  μ {x | f x ≤ M} ≥ μ Set.univ / 2 ∧ μ {x | f x ≥ M} ≥ μ Set.univ / 2

noncomputable def projFirstK (n k : ℕ) (hk : k ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun i => x (Fin.castLE hk i))

noncomputable def normProjFirstK (n k : ℕ) (hk : k ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖projFirstK n k hk x‖

noncomputable def sphereProjNorm (n k : ℕ) (hk : k ≤ n) :
    UnitSphere n → ℝ :=
  fun x => normProjFirstK n k hk (x : EuclideanSpace ℝ (Fin n))

theorem projFirstK_lipschitz (n k : ℕ) (hk : k ≤ n)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖projFirstK n k hk x - projFirstK n k hk y‖ ≤ ‖x - y‖ := by
  simp only [EuclideanSpace.norm_eq, projFirstK]
  apply Real.sqrt_le_sqrt
  have hLHS : ∀ i : Fin k,
    (((WithLp.equiv 2 (Fin k → ℝ)).symm fun j => x (Fin.castLE hk j)) -
     (WithLp.equiv 2 (Fin k → ℝ)).symm fun j => y (Fin.castLE hk j)).ofLp i =
    x (Fin.castLE hk i) - y (Fin.castLE hk i) := by
    intro i; simp [WithLp.equiv, PiLp.sub_apply]
  have hRHS : ∀ j : Fin n, (x - y).ofLp j = x j - y j := by
    intro j; simp [PiLp.sub_apply]
  simp_rw [hLHS, hRHS]
  have h1 : ∑ i : Fin k, ‖x (Fin.castLE hk i) - y (Fin.castLE hk i)‖ ^ 2 =
    ∑ j ∈ Finset.univ.map (Fin.castLEEmb hk), ‖x j - y j‖ ^ 2 := by
    rw [Finset.sum_map]; simp [Fin.castLEEmb]
  rw [h1]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.subset_univ _
  · intro i _ _; positivity

theorem sphereProjNorm_lipschitzWith (n k : ℕ) (hk : k ≤ n) :
    LipschitzWith 1 (sphereProjNorm n k hk) := by
  apply LipschitzWith.mk_one
  intro x y
  simp only [sphereProjNorm, normProjFirstK]
  rw [Real.dist_eq]
  calc |‖projFirstK n k hk ↑x‖ - ‖projFirstK n k hk ↑y‖|
      ≤ ‖projFirstK n k hk ↑x - projFirstK n k hk ↑y‖ := abs_norm_sub_norm_le _ _
    _ ≤ ‖(↑x : EuclideanSpace ℝ (Fin n)) - ↑y‖ := projFirstK_lipschitz n k hk ↑x ↑y
    _ = dist x y := by rw [Subtype.dist_eq, dist_eq_norm]



theorem cthickening_sublevel_of_lipschitz {α : Type*} [PseudoMetricSpace α]
    (f : α → ℝ) (hf : LipschitzWith 1 f)
    (M ε : ℝ) (hε : 0 ≤ ε)
    (hne : {x | f x ≤ M}.Nonempty) :
    Metric.cthickening ε {x | f x ≤ M} ⊆ {x | f x ≤ M + ε} := by
  intro y hy
  simp only [Set.mem_setOf_eq]
  have hinfDist : Metric.infDist y {x | f x ≤ M} ≤ ε := by
    rw [Metric.mem_cthickening_iff] at hy
    have h1 : Metric.infEDist y {x | f x ≤ M} ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy
    calc Metric.infDist y {x | f x ≤ M}
        = (Metric.infEDist y {x | f x ≤ M}).toReal := rfl
      _ ≤ (ENNReal.ofReal ε).toReal :=
          (ENNReal.toReal_le_toReal h1 ENNReal.ofReal_ne_top).mpr hy
      _ = ε := ENNReal.toReal_ofReal hε
  have hbound : f y ≤ M + Metric.infDist y {x | f x ≤ M} := by
    have hNonempty : Nonempty ↥{x | f x ≤ M} := hne.to_subtype
    rw [Metric.infDist_eq_iInf]
    suffices h : ∀ a : ↥{x | f x ≤ M}, f y - M ≤ dist y (a : α) by
      linarith [le_ciInf h]
    intro ⟨a, ha⟩
    simp only [Set.mem_setOf_eq] at ha
    have hLip : dist (f y) (f a) ≤ dist y a := by
      have := hf.dist_le_mul y a; simp at this; exact this
    linarith [show f y - f a ≤ dist y a from
      (le_abs_self _).trans ((Real.dist_eq _ _).symm ▸ hLip)]
  linarith

theorem cthickening_superlevel_of_lipschitz {α : Type*} [PseudoMetricSpace α]
    (f : α → ℝ) (hf : LipschitzWith 1 f)
    (M ε : ℝ) (hε : 0 ≤ ε)
    (hne : {x | f x ≥ M}.Nonempty) :
    Metric.cthickening ε {x | f x ≥ M} ⊆ {x | f x ≥ M - ε} := by
  intro y hy
  simp only [Set.mem_setOf_eq]
  have hinfDist : Metric.infDist y {x | f x ≥ M} ≤ ε := by
    rw [Metric.mem_cthickening_iff] at hy
    have h1 : Metric.infEDist y {x | f x ≥ M} ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy
    calc Metric.infDist y {x | f x ≥ M}
        = (Metric.infEDist y {x | f x ≥ M}).toReal := rfl
      _ ≤ (ENNReal.ofReal ε).toReal :=
          (ENNReal.toReal_le_toReal h1 ENNReal.ofReal_ne_top).mpr hy
      _ = ε := ENNReal.toReal_ofReal hε
  have hbound : f y ≥ M - Metric.infDist y {x | f x ≥ M} := by
    have hNonempty : Nonempty ↥{x | f x ≥ M} := hne.to_subtype
    rw [Metric.infDist_eq_iInf]
    suffices h : ∀ a : ↥{x | f x ≥ M}, M - f y ≤ dist y (a : α) by
      linarith [le_ciInf h]
    intro ⟨a, ha⟩
    simp only [Set.mem_setOf_eq] at ha
    have hLip : dist (f y) (f a) ≤ dist y a := by
      have := hf.dist_le_mul y a; simp at this; exact this
    linarith [show f a - f y ≤ dist y a from
      (show f a - f y ≤ |f y - f a| by linarith [neg_abs_le (f y - f a)]).trans
        ((Real.dist_eq _ _).symm ▸ hLip)]
  linarith











end HighDimensional

open ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace ChernoffHoeffding

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]


def IsBoundedUnitInterval (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  Measurable X ∧ ∀ᵐ ω ∂μ, 0 ≤ X ω ∧ X ω ≤ 1



end ChernoffHoeffding

open scoped InnerProductSpace
open Finset
