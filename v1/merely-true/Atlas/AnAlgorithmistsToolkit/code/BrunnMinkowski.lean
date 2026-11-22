/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Atlas.AnAlgorithmistsToolkit.code.ConvexGeometry

open Pointwise

namespace BrunnMinkowski

def minkowskiSum {α : Type*} [Add α] (A B : Set α) : Set α := A + B

open MeasureTheory Set

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
variable (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant]

omit [MeasurableSpace G] [MeasurableAdd G] in
lemma singleton_add_subset_add {A B : Set G} {a : G} (ha : a ∈ A) :
    {a} + B ⊆ A + B :=
  Set.add_subset_add_right (Set.singleton_subset_iff.mpr ha)

lemma measure_singleton_add (a : G) (B : Set G) :
    μ ({a} + B) = μ B := by
  simp only [singleton_add, image_add_left, measure_preimage_add]

theorem measure_add_ge_right {A B : Set G} (hA : A.Nonempty) :
    μ B ≤ μ (A + B) := by
  obtain ⟨a, ha⟩ := hA
  calc μ B = μ ({a} + B) := (measure_singleton_add μ a B).symm
    _ ≤ μ (A + B) := measure_mono (singleton_add_subset_add ha)

theorem measure_add_ge_left {A B : Set G} (hB : B.Nonempty) :
    μ A ≤ μ (A + B) := by
  obtain ⟨b, hb⟩ := hB
  have hsubset : A + {b} ⊆ A + B :=
    Set.add_subset_add_left (Set.singleton_subset_iff.mpr hb)
  have hmeas : μ (A + {b}) = μ A := by
    simp only [add_singleton, image_add_right, measure_preimage_add_right]
  calc μ A = μ (A + {b}) := hmeas.symm
    _ ≤ μ (A + B) := measure_mono hsubset

theorem measure_add_ge_max {A B : Set G} (hA : A.Nonempty) (hB : B.Nonempty) :
    max (μ A) (μ B) ≤ μ (A + B) :=
  max_le (measure_add_ge_left μ hB) (measure_add_ge_right μ hA)

section Lemma7

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

def bodyOfRevolution (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ × E) :=
  {p | p.1 ∈ s ∧ ‖p.2‖ ≤ f p.1}

theorem convex_bodyOfRevolution {s : Set ℝ} {f : ℝ → ℝ}
    (hs : Convex ℝ s) (hf : ConcaveOn ℝ s f) :
    Convex ℝ (bodyOfRevolution s f : Set (ℝ × E)) := by
  intro p hp q hq a b ha hb hab
  simp only [bodyOfRevolution, Set.mem_setOf_eq] at hp hq ⊢
  refine ⟨hs hp.1 hq.1 ha hb hab, ?_⟩
  have heq1 : (a • p + b • q).1 = a * p.1 + b * q.1 := by simp
  have heq2 : (a • p + b • q).2 = a • p.2 + b • q.2 := by simp
  rw [heq1, heq2]
  calc ‖a • p.2 + b • q.2‖
      ≤ ‖a • p.2‖ + ‖b • q.2‖ := norm_add_le _ _
    _ = a * ‖p.2‖ + b * ‖q.2‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * f p.1 + b * f q.1 := by gcongr <;> [exact hp.2; exact hq.2]
    _ ≤ f (a * p.1 + b * q.1) := hf.2 hp.1 hq.1 ha hb hab

end Lemma7

section BrunnsTheorem

open MeasureTheory

def slice {E : Type*} (K : Set (ℝ × E)) (t : ℝ) : Set E :=
  {x | (t, x) ∈ K}





end BrunnsTheorem

open Real

theorem cone_volume_ratio_le_half (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) / (n + 1)) ^ n ≤ 1 / 2 := by
  have hnn : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (0 : ℝ) < n + 1 := by linarith
  have hbern : (2 : ℝ) ≤ (((n : ℝ) + 1) / n) ^ n := by
    rw [add_div, div_self (ne_of_gt hnn)]
    have ha : (-2 : ℝ) ≤ 1 / (n : ℝ) := by
      have : (0 : ℝ) ≤ 1 / n := div_nonneg one_pos.le hnn.le
      linarith
    have h := one_add_mul_le_pow ha n
    rw [mul_one_div, div_self (ne_of_gt hnn)] at h
    linarith
  rw [div_pow]
  rw [div_le_div_iff₀ (pow_pos hn1 n) (by norm_num : (0 : ℝ) < 2)]
  rw [one_mul]
  rw [div_pow] at hbern
  rw [le_div_iff₀ (pow_pos hnn n)] at hbern
  linarith

theorem exp_neg_one_le_cone_volume_ratio (n : ℕ) (hn : 0 < n) :
    Real.exp (-1) ≤ ((n : ℝ) / (n + 1)) ^ n := by
  have hnn : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (0 : ℝ) < n + 1 := by linarith
  have hq : (0 : ℝ) < n / (n + 1) := div_pos hnn hn1
  have h1 := one_sub_inv_le_log_of_pos hq
  rw [inv_div] at h1
  have h2 : (1 : ℝ) - (↑n + 1) / ↑n = -(1 / ↑n) := by field_simp; ring
  rw [h2] at h1
  have h3 : (↑n : ℝ) * (-(1 / ↑n)) ≤ ↑n * log (↑n / (↑n + 1)) :=
    mul_le_mul_of_nonneg_left h1 hnn.le
  have h4 : (↑n : ℝ) * (-(1 / ↑n)) = -1 := by field_simp
  rw [h4] at h3
  rw [← log_pow] at h3
  rwa [le_log_iff_exp_le (pow_pos hq n)] at h3

theorem cone_centroid_cut_bounds (n : ℕ) (hn : 0 < n) :
    Real.exp (-1) ≤ ((n : ℝ) / (n + 1)) ^ n ∧
    ((n : ℝ) / (n + 1)) ^ n ≤ 1 / 2 :=
  ⟨exp_neg_one_le_cone_volume_ratio n hn, cone_volume_ratio_le_half n hn⟩


open Finset Real

theorem brunn_minkowski_boxes {n : ℕ} (hn : 0 < n)
    (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    (∏ i : Fin n, (a i + b i)) ^ ((1 : ℝ) / ↑n) ≥
      (∏ i : Fin n, a i) ^ ((1 : ℝ) / ↑n) +
      (∏ i : Fin n, b i) ^ ((1 : ℝ) / ↑n) := by
  have hab : ∀ i, (0 : ℝ) < a i + b i := fun i => add_pos (ha i) (hb i)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h1n_pos : (0 : ℝ) < 1 / ↑n := div_pos one_pos hn_pos
  have hprod_ab_pos : (0 : ℝ) < ∏ i : Fin n, (a i + b i) :=
    Finset.prod_pos (fun i _ => hab i)
  have hprod_a_pos : (0 : ℝ) < ∏ i : Fin n, a i :=
    Finset.prod_pos (fun i _ => ha i)
  have hprod_b_pos : (0 : ℝ) < ∏ i : Fin n, b i :=
    Finset.prod_pos (fun i _ => hb i)

  have hw_sum : ∑ _i : Fin n, ((1 : ℝ) / ↑n) = 1 := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hn_ne]
  have hz_a_nn : ∀ i : Fin n, (0 : ℝ) ≤ a i / (a i + b i) :=
    fun i => div_nonneg (le_of_lt (ha i)) (le_of_lt (hab i))
  have hz_b_nn : ∀ i : Fin n, (0 : ℝ) ≤ b i / (a i + b i) :=
    fun i => div_nonneg (le_of_lt (hb i)) (le_of_lt (hab i))
  have hw_nn : ∀ i ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ (1 : ℝ) / ↑n :=
    fun _ _ => le_of_lt h1n_pos

  have hamgm_a : ∏ i : Fin n, (a i / (a i + b i)) ^ ((1 : ℝ) / ↑n) ≤
      ∑ i : Fin n, (1 / ↑n) * (a i / (a i + b i)) :=
    Real.geom_mean_le_arith_mean_weighted _ (fun _ => (1 : ℝ) / ↑n)
      (fun i => a i / (a i + b i)) hw_nn hw_sum (fun i _ => hz_a_nn i)

  have hamgm_b : ∏ i : Fin n, (b i / (a i + b i)) ^ ((1 : ℝ) / ↑n) ≤
      ∑ i : Fin n, (1 / ↑n) * (b i / (a i + b i)) :=
    Real.geom_mean_le_arith_mean_weighted _ (fun _ => (1 : ℝ) / ↑n)
      (fun i => b i / (a i + b i)) hw_nn hw_sum (fun i _ => hz_b_nn i)

  have hsum_eq_one : (∑ i : Fin n, (1 / ↑n) * (a i / (a i + b i))) +
      (∑ i : Fin n, (1 / ↑n) * (b i / (a i + b i))) = 1 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← mul_add]
    have : ∀ i : Fin n, a i / (a i + b i) + b i / (a i + b i) = 1 := by
      intro i
      rw [← add_div, div_self (ne_of_gt (hab i))]
    simp_rw [this, mul_one]
    exact hw_sum

  have hprod_a_div : ∏ i : Fin n, (a i / (a i + b i)) ^ ((1 : ℝ) / ↑n) =
      (∏ i : Fin n, a i) ^ ((1 : ℝ) / ↑n) / (∏ i : Fin n, (a i + b i)) ^ ((1 : ℝ) / ↑n) := by
    rw [Real.finset_prod_rpow Finset.univ (fun i => a i / (a i + b i))
        (fun i _ => hz_a_nn i) ((1 : ℝ) / ↑n)]
    rw [show ∏ i : Fin n, (a i / (a i + b i)) = (∏ i : Fin n, a i) / (∏ i : Fin n, (a i + b i))
        from Finset.prod_div_distrib (fun i => a i) (fun i => a i + b i)]
    exact Real.div_rpow (le_of_lt hprod_a_pos) (le_of_lt hprod_ab_pos) _
  have hprod_b_div : ∏ i : Fin n, (b i / (a i + b i)) ^ ((1 : ℝ) / ↑n) =
      (∏ i : Fin n, b i) ^ ((1 : ℝ) / ↑n) / (∏ i : Fin n, (a i + b i)) ^ ((1 : ℝ) / ↑n) := by
    rw [Real.finset_prod_rpow Finset.univ (fun i => b i / (a i + b i))
        (fun i _ => hz_b_nn i) ((1 : ℝ) / ↑n)]
    rw [show ∏ i : Fin n, (b i / (a i + b i)) = (∏ i : Fin n, b i) / (∏ i : Fin n, (a i + b i))
        from Finset.prod_div_distrib (fun i => b i) (fun i => a i + b i)]
    exact Real.div_rpow (le_of_lt hprod_b_pos) (le_of_lt hprod_ab_pos) _

  have hprod_ab_rpow_pos : (0 : ℝ) < (∏ i : Fin n, (a i + b i)) ^ ((1 : ℝ) / ↑n) :=
    rpow_pos_of_pos hprod_ab_pos _

  rw [ge_iff_le]
  suffices h : (∏ i : Fin n, a i) ^ ((1 : ℝ) / ↑n) /
      (∏ i : Fin n, (a i + b i)) ^ ((1 : ℝ) / ↑n) +
      (∏ i : Fin n, b i) ^ ((1 : ℝ) / ↑n) /
      (∏ i : Fin n, (a i + b i)) ^ ((1 : ℝ) / ↑n) ≤ 1 by
    rwa [← add_div, div_le_one hprod_ab_rpow_pos] at h

  calc (∏ i : Fin n, a i) ^ ((1 : ℝ) / ↑n) /
        (∏ i : Fin n, (a i + b i)) ^ ((1 : ℝ) / ↑n) +
        (∏ i : Fin n, b i) ^ ((1 : ℝ) / ↑n) /
        (∏ i : Fin n, (a i + b i)) ^ ((1 : ℝ) / ↑n)
      = ∏ i : Fin n, (a i / (a i + b i)) ^ ((1 : ℝ) / ↑n) +
        ∏ i : Fin n, (b i / (a i + b i)) ^ ((1 : ℝ) / ↑n) := by
          rw [← hprod_a_div, ← hprod_b_div]
    _ ≤ (∑ i : Fin n, (1 / ↑n) * (a i / (a i + b i))) +
        (∑ i : Fin n, (1 / ↑n) * (b i / (a i + b i))) :=
          add_le_add hamgm_a hamgm_b
    _ = 1 := hsum_eq_one

section Fact8

variable {m : ℕ}

lemma volume_singleton_add' (a : Fin (m + 1) → ℝ) (s : Set (Fin (m + 1) → ℝ)) :
    volume ({a} + s) = volume s := by
  rw [Set.singleton_add, Set.image_add_left, measure_preimage_add]

lemma volume_add_singleton' (s : Set (Fin (m + 1) → ℝ)) (b : Fin (m + 1) → ℝ) :
    volume (s + {b}) = volume s := by
  rw [Set.add_singleton, Set.image_add_right, measure_preimage_add_right]

lemma volume_hyperplane (c : ℝ) :
    volume ({x : Fin (m + 1) → ℝ | x 0 = c}) = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun (_ : Fin (m + 1)) => (volume : Measure ℝ)) (0 : Fin (m + 1)) c

lemma intersection_subset_hyperplane (A B : Set (Fin (m + 1) → ℝ))
    (a₀ : Fin (m + 1) → ℝ) (ha₀_max : ∀ a ∈ A, a 0 ≤ a₀ 0)
    (b₀ : Fin (m + 1) → ℝ) (hb₀_min : ∀ b ∈ B, b₀ 0 ≤ b 0) :
    (A + {b₀}) ∩ ({a₀} + B) ⊆ {x | x 0 = a₀ 0 + b₀ 0} := by
  intro x hx
  have hx1 := hx.1
  have hx2 := hx.2
  rw [Set.mem_add] at hx1 hx2
  obtain ⟨a, ha, c, hc, hxac⟩ := hx1
  obtain ⟨d, hd, b, hb, hxdb⟩ := hx2
  rw [Set.mem_singleton_iff] at hc hd
  simp only [Set.mem_setOf_eq]
  have h1 : a 0 ≤ a₀ 0 := ha₀_max a ha
  have h2 : b₀ 0 ≤ b 0 := hb₀_min b hb
  have hab : a 0 + b₀ 0 = a₀ 0 + b 0 := by
    have : (a + c) 0 = (d + b) 0 := by rw [hxac, hxdb]
    simp only [Pi.add_apply] at this
    rw [hc, hd] at this
    exact this
  have hx0 : x 0 = a 0 + b₀ 0 := by
    rw [← hxac]; simp only [Pi.add_apply, hc]
  rw [hx0]; linarith

theorem volume_add_le_volume_minkowski_sum (A B : Set (Fin (m + 1) → ℝ))
    (hA_compact : IsCompact A) (hA_ne : A.Nonempty)
    (hB_compact : IsCompact B) (hB_ne : B.Nonempty) (hB_meas : MeasurableSet B) :
    volume A + volume B ≤ volume (A + B) := by
  obtain ⟨a₀, ha₀, ha₀_max⟩ := hA_compact.exists_isMaxOn hA_ne
    (continuous_apply (0 : Fin (m + 1))).continuousOn
  obtain ⟨b₀, hb₀, hb₀_min⟩ := hB_compact.exists_isMinOn hB_ne
    (continuous_apply (0 : Fin (m + 1))).continuousOn
  have h_sub_AB : A + {b₀} ⊆ A + B :=
    Set.add_subset_add_left (Set.singleton_subset_iff.mpr hb₀)
  have h_sub_aB : {a₀} + B ⊆ A + B :=
    Set.add_subset_add_right (Set.singleton_subset_iff.mpr ha₀)
  have h_union_sub : (A + {b₀}) ∪ ({a₀} + B) ⊆ A + B :=
    Set.union_subset h_sub_AB h_sub_aB
  have h_ae_disj : AEDisjoint volume (A + {b₀}) ({a₀} + B) :=
    measure_mono_null
      (intersection_subset_hyperplane A B a₀ (fun a ha => ha₀_max ha) b₀ (fun b hb => hb₀_min hb))
      (volume_hyperplane _)
  have h_meas_aB : MeasurableSet ({a₀} + B) := by
    rw [Set.singleton_add, Set.image_add_left]
    exact measurable_const_add (-a₀) hB_meas
  calc volume A + volume B
      = volume (A + {b₀}) + volume ({a₀} + B) := by
          rw [volume_add_singleton' A b₀, volume_singleton_add' a₀ B]
    _ = volume ((A + {b₀}) ∪ ({a₀} + B)) :=
          (measure_union₀ h_meas_aB.nullMeasurableSet h_ae_disj).symm
    _ ≤ volume (A + B) := measure_mono h_union_sub

end Fact8

end BrunnMinkowski

namespace GrunbaumsTheorem

open MeasureTheory Set Real

variable {n : ℕ}

noncomputable def centroid (K : Set (Fin (n + 1) → ℝ)) : Fin (n + 1) → ℝ :=
  ((volume K).toReal)⁻¹ • ∫ x in K, x ∂volume

def closedHalfspace (f : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {x | f x ≤ c}


end GrunbaumsTheorem

namespace IsoperimetricInequality

open MeasureTheory Metric Set Real Pointwise

noncomputable def modulusOfConvexity (ε : ℝ) : ℝ :=
  1 - Real.sqrt (1 - ε ^ 2 / 4)


end IsoperimetricInequality

namespace GrunbaumConeReplacement

open MeasureTheory Set

noncomputable def volumeRatio {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (K L : Set α) : ENNReal :=
  μ (K ∩ L) / μ K

def posHalfSpace (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | 0 ≤ x 0}

theorem volumeRatio_eq_of_measures_eq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {K C L : Set α}
    (hvol_total : μ K = μ C)
    (hvol_part : μ (K ∩ L) = μ (C ∩ L)) :
    volumeRatio μ K L = volumeRatio μ C L := by
  simp only [volumeRatio, hvol_part, hvol_total]

theorem volumeRatio_mono_right {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (K : Set α) {L₁ L₂ : Set α} (h : L₁ ⊆ L₂) :
    volumeRatio μ K L₁ ≤ volumeRatio μ K L₂ := by
  apply ENNReal.div_le_div_right
  exact measure_mono (Set.inter_subset_inter_right K h)

theorem volume_ratio_chain {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {K C L L' : Set α} {b : ENNReal}
    (hvol_total : μ K = μ C)
    (hvol_part : μ (K ∩ L) = μ (C ∩ L))
    (hL' : L' ⊆ L)
    (hbound : b ≤ volumeRatio μ C L') :
    b ≤ volumeRatio μ K L := by
  have heq := volumeRatio_eq_of_measures_eq μ hvol_total hvol_part
  have hmono := volumeRatio_mono_right μ C hL'
  calc b ≤ volumeRatio μ C L' := hbound
    _ ≤ volumeRatio μ C L := hmono
    _ = volumeRatio μ K L := heq.symm



end GrunbaumConeReplacement

namespace GrunbaumsTheorem

open MeasureTheory Set Real

variable {n : ℕ}


end GrunbaumsTheorem
