/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.InvarianceDefs

noncomputable section

open MeasureTheory Measure Finset BigOperators ENNReal

namespace BooleanFourier

def rademacherMeasure : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac (-1 : ℝ) + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (1 : ℝ)

instance rademacherMeasure_isFiniteMeasure : IsFiniteMeasure rademacherMeasure := by
  constructor
  simp only [rademacherMeasure, Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply]
  simp

instance rademacherMeasure_sigmaFinite : SigmaFinite rademacherMeasure :=
  @IsFiniteMeasure.toSigmaFinite _ _ rademacherMeasure _

def hybridMeasure (n : ℕ) (k : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i : Fin n =>
    if i.val < k then ProbabilityTheory.gaussianReal 0 1 else rademacherMeasure)

theorem hybridMeasure_zero (n : ℕ) :
    hybridMeasure n 0 = Measure.pi (fun _ : Fin n => rademacherMeasure) := by
  simp [hybridMeasure]

theorem hybridMeasure_n (n : ℕ) :
    hybridMeasure n n = GaussianHypercontractivity.stdGaussianMeasure n := by
  simp only [hybridMeasure, GaussianHypercontractivity.stdGaussianMeasure]
  congr 1
  funext i
  simp [i.isLt]

def hybridExpectation {n : ℕ} (f : (Fin n → Bool) → ℝ) (Ψ : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ z : Fin n → ℝ, Ψ (multilinearExtension f z) ∂(hybridMeasure n k)

theorem hybridExpectation_n {n : ℕ} (f : (Fin n → Bool) → ℝ) (Ψ : ℝ → ℝ) :
    hybridExpectation f Ψ n = gaussianExpectation f Ψ := by
  simp only [hybridExpectation, gaussianExpectation, hybridMeasure_n]

def boolToRealVec {n : ℕ} (b : Fin n → Bool) : Fin n → ℝ :=
  fun i => boolToReal (b i)

lemma pi_rademacher_eq_sum_dirac (n : ℕ) :
    Measure.pi (fun _ : Fin n => rademacherMeasure) =
      ((2 : ℝ≥0∞)⁻¹ ^ n) • ∑ b : Fin n → Bool, Measure.dirac (boolToRealVec b) := by
  open Classical in
  apply @Measure.pi_eq (Fin n) (fun _ => ℝ) _ _ (fun _ : Fin n => rademacherMeasure)
    (fun _ => rademacherMeasure_sigmaFinite)
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul]
  have hpi_meas : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  conv_lhs =>
    rw [show (∑ b : Fin n → Bool, Measure.dirac (boolToRealVec b)) (Set.univ.pi s) =
      ∑ b : Fin n → Bool, (Measure.dirac (boolToRealVec b)) (Set.univ.pi s) from by
      have : (∑ b : Fin n → Bool, Measure.dirac (boolToRealVec b)) =
        ∑ b ∈ Finset.univ, Measure.dirac (boolToRealVec b) := by simp
      rw [this, Measure.coe_finset_sum]; simp]
  simp only [Measure.dirac_apply' _ hpi_meas, Set.indicator_apply, Pi.one_apply,
    Set.mem_univ_pi, boolToRealVec]
  simp_rw [show ∀ x : Fin n → Bool,
      (if ∀ i : Fin n, boolToReal (x i) ∈ s i then (1 : ℝ≥0∞) else 0) =
      ∏ i : Fin n, (if boolToReal (x i) ∈ s i then 1 else 0) from fun x => by
    rw [Finset.prod_boole]; simp]
  have swap : ∑ x : Fin n → Bool,
      ∏ i : Fin n, (if boolToReal (x i) ∈ s i then (1 : ℝ≥0∞) else 0) =
      ∏ i : Fin n, ∑ b : Bool, (if boolToReal b ∈ s i then 1 else 0) := by
    have h := @Finset.prod_univ_sum (Fin n) ℝ≥0∞ _ _ (fun _ => Bool) _
      (fun _ => Finset.univ) (fun i b => if boolToReal b ∈ s i then 1 else 0)
    rw [Fintype.piFinset_univ] at h; exact h.symm
  rw [swap, show (2 : ℝ≥0∞)⁻¹ ^ n = ∏ _i : Fin n, (2 : ℝ≥0∞)⁻¹ from by
    simp [Finset.prod_const]]
  rw [← Finset.prod_mul_distrib]
  congr 1; funext i
  simp only [rademacherMeasure, Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (hs i), Set.indicator_apply, Pi.one_apply]
  rw [Fintype.sum_bool]
  simp only [boolToReal, ite_true, Bool.false_eq_true, ite_false]
  ring


theorem integral_pi_rademacher {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    ∫ z : Fin n → ℝ, g z ∂(Measure.pi (fun _ : Fin n => rademacherMeasure)) =
      (1 / (2 : ℝ) ^ n) * ∑ b : Fin n → Bool, g (boolToRealVec b) := by
  rw [pi_rademacher_eq_sum_dirac]
  rw [integral_smul_measure]
  rw [show (∑ b : Fin n → Bool, Measure.dirac (boolToRealVec b)) =
    ∑ b ∈ Finset.univ, Measure.dirac (boolToRealVec b) from by simp]
  rw [integral_finset_sum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac]
  congr 1
  simp [ENNReal.toReal_pow, ENNReal.toReal_inv]

theorem hybridExpectation_zero {n : ℕ} (f : (Fin n → Bool) → ℝ) (Ψ : ℝ → ℝ) :
    hybridExpectation f Ψ 0 = booleanExpectation f Ψ := by
  unfold hybridExpectation booleanExpectation
  rw [hybridMeasure_zero]
  rw [integral_pi_rademacher]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  exact multilinearExtension_eq_on_boolToReal f b

theorem lindeberg_telescoping {n : ℕ} (f : (Fin n → Bool) → ℝ) (Ψ : ℝ → ℝ) :
    booleanExpectation f Ψ - gaussianExpectation f Ψ =
      ∑ k : Fin n, (hybridExpectation f Ψ k.val - hybridExpectation f Ψ (k.val + 1)) := by
  rw [← hybridExpectation_zero f Ψ, ← hybridExpectation_n f Ψ]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => hybridExpectation f Ψ i - hybridExpectation f Ψ (i + 1)) n]
  exact (Finset.sum_range_sub' (fun i => hybridExpectation f Ψ i) n).symm

end BooleanFourier

end
