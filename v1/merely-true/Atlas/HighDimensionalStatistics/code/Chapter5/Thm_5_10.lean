/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory

open MeasureTheory InformationTheory Finset Real

noncomputable section

namespace FanoInequality

/-- Uniform mixture measure `M⁻¹ ∑_j P j` over `M` probability measures. -/
noncomputable def mixtureMeasure {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (P : Fin M → Measure Ω) : Measure Ω :=
  (M : ENNReal)⁻¹ • ∑ j : Fin M, P j

/-- The local `mixtureMeasure` agrees with `InfoTheory.mixtureMeasure`. -/
lemma mixtureMeasure_eq_infoTheory {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (P : Fin M → Measure Ω) :
    mixtureMeasure P = InfoTheory.mixtureMeasure M P := by
  unfold mixtureMeasure InfoTheory.mixtureMeasure
  rw [one_div]

/-- Fano-type bound stated in terms of average KL to the uniform mixture: for
every measurable classifier `ψ : Ω → Fin M`, some hypothesis `P j` has error
probability `P_j(ψ ≠ j) ≥ 1 - (avg KL to mixture + log 2) / log(M - 1)`. -/
theorem fano_lemma {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 3 ≤ M)
    (P : Fin M → Measure Ω)
    [∀ j, IsProbabilityMeasure (P j)]
    (hac : ∀ j k, P j ≪ P k)
    (hfin : ∀ j k, klDiv (P j) (P k) ≠ ⊤) :
    ∀ (ψ : Ω → Fin M), Measurable ψ →
      ∃ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal ≥
        1 - ((1 / (M : ℝ)) * ∑ j : Fin M,
          (klDiv (P j) (mixtureMeasure P)).toReal + Real.log 2) /
          Real.log ((M : ℝ) - 1) := by
  intro ψ hψ
  simp_rw [mixtureMeasure_eq_infoTheory]
  have hfin_kl : ∀ j, klDiv (P j) (InfoTheory.mixtureMeasure M P) ≠ ⊤ :=
    fun j => InfoTheory.klDiv_mixture_ne_top M (by omega) P hac hfin j
  exact InfoTheory.fano_lemma M hM P hfin_kl ψ hψ

/-- The average KL divergence to the uniform mixture is bounded by the average
pairwise KL divergence: `M⁻¹ ∑_j KL(P_j ‖ P̄) ≤ M⁻² ∑_{j,k} KL(P_j ‖ P_k)`. -/
theorem kl_mixture_le_avg_pairwise {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω)
    [∀ j, IsProbabilityMeasure (P j)]
    (hac : ∀ j k, P j ≪ P k)
    (hfin : ∀ j k, klDiv (P j) (P k) ≠ ⊤) :
    (1 / (M : ℝ)) * ∑ j : Fin M,
      (klDiv (P j) (mixtureMeasure P)).toReal ≤
    (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M,
      (klDiv (P j) (P k)).toReal := by
  simp_rw [mixtureMeasure_eq_infoTheory]
  exact InfoTheory.kl_mixture_le_avg_pairwise M hM P hac hfin

/-- Entropy-form Fano inequality: the average error probability times
`log(M - 1)` plus `log 2` is at least `log M - M⁻² ∑_{j,k} KL(P_j ‖ P_k)`. -/
lemma fano_avg_numerator_bound {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω) [∀ j, IsProbabilityMeasure (P j)]
    (hac : ∀ j k, P j ≪ P k)
    (hfin : ∀ j k, klDiv (P j) (P k) ≠ ⊤)
    (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    ((1 / (M : ℝ)) * ∑ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal) *
      Real.log ((M : ℝ) - 1) + Real.log 2 ≥
    Real.log (M : ℝ) - (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M,
      (klDiv (P j) (P k)).toReal := by

  have hfin_kl : ∀ j, klDiv (P j) (InfoTheory.mixtureMeasure M P) ≠ ⊤ :=
    fun j => InfoTheory.klDiv_mixture_ne_top M hM P hac hfin j
  have h_core := InfoTheory.fano_entropy_core_bound M hM P hfin_kl ψ hψ


  have h_kl : (1 / (M : ℝ)) * ∑ j : Fin M,
      (klDiv (P j) (InfoTheory.mixtureMeasure M P)).toReal ≤
    (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M,
      (klDiv (P j) (P k)).toReal := by
    have := kl_mixture_le_avg_pairwise M hM P hac hfin
    simp_rw [mixtureMeasure_eq_infoTheory] at this
    exact this

  linarith

/-- Fano's inequality (Theorem 5.10): for any measurable classifier
`ψ : Ω → Fin M`, some hypothesis `P j` has error
`P_j(ψ ≠ j) ≥ 1 - (M⁻² ∑_{j,k} KL(P_j ‖ P_k) + log 2) / log(M - 1)`. -/
theorem fano_inequality {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 3 ≤ M)
    (P : Fin M → Measure Ω)
    [∀ j, IsProbabilityMeasure (P j)]
    (hac : ∀ j k, P j ≪ P k)
    (hfin : ∀ j k, klDiv (P j) (P k) ≠ ⊤) :

    ∀ (ψ : Ω → Fin M), Measurable ψ →


      ∃ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal ≥
        1 - ((1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M,
          (klDiv (P j) (P k)).toReal + Real.log 2) / Real.log ((M : ℝ) - 1) := by
  intro ψ hψ

  obtain ⟨j, hj⟩ := fano_lemma M hM P hac hfin ψ hψ
  refine ⟨j, le_trans ?_ hj⟩

  have hM2 : 2 ≤ M := by omega
  have hkl := kl_mixture_le_avg_pairwise M hM2 P hac hfin

  have hlog : 0 ≤ Real.log ((M : ℝ) - 1) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ (M : ℝ) := Nat.ofNat_le_cast.mpr hM2
    linarith

  have hsums : (1 / (M : ℝ)) * ∑ j : Fin M,
      (klDiv (P j) (mixtureMeasure P)).toReal + Real.log 2 ≤
    (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M,
      (klDiv (P j) (P k)).toReal + Real.log 2 := by linarith

  linarith [div_le_div_of_nonneg_right hsums hlog]

end FanoInequality
