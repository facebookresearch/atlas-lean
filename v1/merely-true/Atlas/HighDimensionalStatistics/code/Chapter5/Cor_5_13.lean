/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.ExponentialBounds
import Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8

open MeasureTheory InformationTheory

noncomputable section

namespace GaussianSequenceModel

/-- Squared Euclidean distance between two vectors in `ℝ^d`. -/
def sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (θ₁ i - θ₂ i) ^ 2

/-- An estimator is a function mapping observations in `ℝ^d` to a parameter estimate in `ℝ^d`. -/
def Estimator (d : ℕ) := (Fin d → ℝ) → (Fin d → ℝ)

/-- `Estimator d` is nonempty (witnessed by the identity). -/
instance {d : ℕ} : Nonempty (Estimator d) := ⟨id⟩

/-- The identity estimator `θ̂(Y) = Y` (least squares in the Gaussian sequence model). -/
def identityEstimator (d : ℕ) : Estimator d := id

/-- Risk of an estimator `θ̂` at parameter `θ`: the expected squared distance
`E[‖θ̂(Y) - θ‖²]` under `P θ`. -/
def risk {d : ℕ} (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (θhat : Estimator d) (θ : Fin d → ℝ) : ℝ :=
  ∫ Y, sqDist (θhat Y) θ ∂(P θ)

/-- Worst-case risk of `θ̂` over the parameter set `Θ`. -/
def supRisk {d : ℕ} (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (Θ : Set (Fin d → ℝ)) (θhat : Estimator d) : ℝ :=
  ⨆ θ ∈ Θ, risk P θhat θ

/-- Minimax risk over `Θ`: the infimum of the worst-case risk over all measurable estimators. -/
def minimaxRisk {d : ℕ} (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (Θ : Set (Fin d → ℝ)) : ℝ :=
  ⨅ (θhat : { f : Estimator d // Measurable f }), supRisk P Θ θhat.val

/-- The `ℓ¹`-norm `|θ|_1 = ∑_i |θ_i|`. -/
def l1norm {d : ℕ} (θ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, |θ i|

/-- Structural property recording that a family `P : ℝ^d → Measure ℝ^d` is a Gaussian sequence
model with noise level `σ` and sample size `n`: each `P θ` is a probability measure with the
expected coordinate-wise variance, mean, KL/density-ratio structure, and integrability
properties required to run the minimax arguments of Chapter 5. -/
structure IsGSM {d : ℕ} (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (σ : ℝ) (n : ℕ) : Prop where
  isProbabilityMeasure : ∀ (hσ : 0 < σ) (hn : 0 < n) (θ : Fin d → ℝ),
    IsProbabilityMeasure (P θ)
  identity_risk_coord : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θ : Fin d → ℝ) (i : Fin d),
    ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n
  coord_mean : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θ : Fin d → ℝ) (i : Fin d),
    ∫ Y, Y i ∂(P θ) = θ i
  density_ratio : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θ₁ θ₂ : Fin d → ℝ), P θ₁ = (P θ₂).withDensity (fun Y =>
      ENNReal.ofReal (Real.exp ((↑n / (2 * σ ^ 2)) *
        ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2))))
  integrable_sqDist : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
    Integrable (fun Y => sqDist (θhat Y) θ) (P θ)
  bddAbove_risk : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
    BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ (Set.univ : Set (Fin d → ℝ))),
      ∫ Y, sqDist (θhat Y) θ ∂(P θ))
  hP_kl_ne_top : ∀ (θ₀ θ₁ : Fin d → ℝ),
    InformationTheory.klDiv (P θ₁) (P θ₀) ≠ ⊤

  expected_cross_term_bound : ∀ (hσ : 0 < σ) (hn : 0 < n) (hd : 0 < d)
    (R : ℝ) (hR : 0 < R)
    (θ θ' : Fin d → ℝ)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ))
    (hθ' : l1norm θ' ≤ R)
    (hθhat : ∀ Y, l1norm (θhat Y) ≤ R),
    ∫ Y, ∑ i : Fin d, (θhat Y i - θ' i) * (Y i - θ i) ∂(P θ) ≤
      (σ ^ 2 / ↑n) * (R * Real.log ↑d / σ)
  integrable_cross_term : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ θ' : Fin d → ℝ),
    Integrable (fun Y => ∑ i : Fin d, (θhat Y i - θ' i) * (Y i - θ i)) (P θ)

/-- Pointwise oracle inequality: if `θhatY` minimizes the squared error to `Y` better than `θ'`,
then `‖θhatY - θ‖² ≤ ‖θ' - θ‖² + 2 ∑_i (θhatY_i - θ'_i)(Y_i - θ_i)`. -/
lemma oracle_ineq_pointwise {d : ℕ} (θ θ' θhatY Y : Fin d → ℝ)
    (hopt : sqDist Y θhatY ≤ sqDist Y θ') :
    sqDist θhatY θ ≤ sqDist θ' θ +
      2 * ∑ i : Fin d, (θhatY i - θ' i) * (Y i - θ i) := by
  unfold sqDist at *
  have key : ∀ i : Fin d,
      (θhatY i - θ i) ^ 2 = (θ' i - θ i) ^ 2 +
      ((Y i - θhatY i) ^ 2 - (Y i - θ' i) ^ 2) + 2 * ((θhatY i - θ' i) * (Y i - θ i)) := by
    intro i; ring
  simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith [show ∑ i : Fin d, ((Y i - θhatY i) ^ 2 - (Y i - θ' i) ^ 2) ≤ 0 from by
    rw [Finset.sum_sub_distrib]; linarith]

/-- Expected oracle inequality for a constrained least-squares estimator over an `ℓ¹`-ball of
radius `R`: bounds the risk at `θ` by `‖θ' - θ‖² + 2(σ²/n)(R log d / σ)`. -/
theorem IsGSM.cross_term_bound {d : ℕ}
    {P : (Fin d → ℝ) → Measure (Fin d → ℝ)} {σ : ℝ} {n : ℕ}
    (hP : IsGSM P σ n) (hσ : 0 < σ) (hn : 0 < n) (hd : 0 < d)
    (R : ℝ) (hR : 0 < R)
    (θ θ' : Fin d → ℝ)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ))
    (hθ' : l1norm θ' ≤ R)
    (hθhat : ∀ Y, l1norm (θhat Y) ≤ R)
    (hopt : ∀ Y, ∀ u : Fin d → ℝ, l1norm u ≤ R → sqDist Y (θhat Y) ≤ sqDist Y u) :
    ∫ Y, sqDist (θhat Y) θ ∂(P θ) ≤
      sqDist θ' θ + 2 * (σ ^ 2 / ↑n) * (R * Real.log ↑d / σ) := by


  have hpw : ∀ Y, sqDist (θhat Y) θ ≤
      sqDist θ' θ + 2 * ∑ i : Fin d, (θhat Y i - θ' i) * (Y i - θ i) := by
    intro Y
    exact oracle_ineq_pointwise θ θ' (θhat Y) Y (hopt Y θ' hθ')


  haveI := hP.isProbabilityMeasure hσ hn θ
  have h_int_sq := hP.integrable_sqDist hσ hn θhat θ
  have h_int_ct := hP.integrable_cross_term hσ hn θhat θ θ'
  have h_int_rhs : Integrable
      (fun Y => sqDist θ' θ + 2 * ∑ i : Fin d, (θhat Y i - θ' i) * (Y i - θ i)) (P θ) :=
    integrable_const (sqDist θ' θ) |>.add (h_int_ct.const_mul 2)
  have h_le := integral_mono h_int_sq h_int_rhs (fun Y => hpw Y)


  rw [integral_add (integrable_const _) (h_int_ct.const_mul 2),
      integral_const, MeasureTheory.integral_const_mul] at h_le
  simp only [MeasureTheory.Measure.real, MeasureTheory.IsProbabilityMeasure.measure_univ,
    ENNReal.toReal_one, smul_eq_mul, one_mul] at h_le

  have h_ct := hP.expected_cross_term_bound hσ hn hd R hR θ θ' θhat hθ' hθhat

  nlinarith

/-- In a Gaussian sequence model, `P θ₁` is absolutely continuous with respect to `P θ₂`. -/
theorem gsm_abs_continuous {d : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (hP : IsGSM P σ n)
    (θ₁ θ₂ : Fin d → ℝ) :
    P θ₁ ≪ P θ₂ := by
  haveI : ∀ θ, IsProbabilityMeasure (P θ) := fun θ => hP.isProbabilityMeasure hσ hn θ
  exact (InfoTheory.gaussian_family_llr_integral σ hσ n hn P
    (fun θ i => hP.identity_risk_coord hσ hn θ i)
    (fun θ₁ θ₂ => hP.density_ratio hσ hn θ₁ θ₂)
    (fun θ i => hP.coord_mean hσ hn θ i) θ₁ θ₂).1

/-- The squared-distance loss `Y ↦ ‖θ̂(Y) - θ‖²` is integrable under `P θ` in a GSM. -/
theorem gsm_integrable_sqDist {d : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (hP : IsGSM P σ n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ) :
    Integrable (fun Y => sqDist (θhat Y) θ) (P θ) :=
  hP.integrable_sqDist hσ hn θhat θ

/-- The squared-distance loss is almost-everywhere strongly measurable under `P θ` in a GSM. -/
theorem gsm_measurable_sqDist {d : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (hP : IsGSM P σ n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ) :
    AEStronglyMeasurable (fun Y => sqDist (θhat Y) θ) (P θ) :=
  (gsm_integrable_sqDist P σ hσ n hn hP θhat θ).aestronglyMeasurable

/-- The supremum of risks of `θhat` over `θ ∈ univ` is bounded above in a GSM. -/
theorem gsm_bddAbove_risk {d : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (hP : IsGSM P σ n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)) :
    BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ (Set.univ : Set (Fin d → ℝ))),
      ∫ Y, sqDist (θhat Y) θ ∂(P θ)) :=
  hP.bddAbove_risk hσ hn θhat

/-- Auxiliary numerical bound used in the Fano argument when `log(M - 1)` is positive:
`1 - (d/64 + log 2) / log(M-1) ≥ 1/4` under the Varshamov-Gilbert hypotheses on `M`. -/
theorem fano_numerical_bound_pos_log (d M : ℕ) (hd : 0 < d)
    (hM : (M : ℝ) ≥ Real.exp ((1/4 : ℝ) ^ 2 * ↑d / 2))
    (hM4 : 4 ≤ M)
    (hlog_vg : Real.log ((M : ℝ) - 1) ≥ ↑d / 8)
    (h_log : 0 < Real.log ((M : ℝ) - 1)) :
    (1 : ℝ) - ((↑d / 64 : ℝ) + Real.log 2) / Real.log ((M : ℝ) - 1) ≥ 1 / 4 := by


  rw [ge_iff_le, ← sub_nonneg]
  have key : (1 : ℝ) - (↑d / 64 + Real.log 2) / Real.log ((M : ℝ) - 1) - 1/4 =
      (3/4 * Real.log ((M : ℝ) - 1) - (↑d / 64 + Real.log 2)) / Real.log ((M : ℝ) - 1) := by
    field_simp; ring
  rw [key]
  apply div_nonneg _ (le_of_lt h_log)

  linarith [show ↑d / 16 + 4 * Real.log 2 ≤ 3 * Real.log ((M : ℝ) - 1) from by
    by_cases hd8 : d ≤ 8
    ·
      have hM1_ge_3 : (M : ℝ) - 1 ≥ 3 := by
        have : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4
        linarith
      have hlog_ge : Real.log ((M : ℝ) - 1) ≥ Real.log 3 :=
        Real.log_le_log (by norm_num) hM1_ge_3
      have hd_le : (↑d : ℝ) / 16 ≤ 1/2 := by
        have : (d : ℝ) ≤ 8 := by exact_mod_cast hd8
        linarith


      have h_num : 1/2 + 4 * Real.log 2 ≤ 3 * Real.log 3 := by
        have h1 : 1/2 + 4 * Real.log 2 = Real.log (16 * Real.exp (1/2)) := by
          rw [Real.log_mul (by norm_num : (16:ℝ) ≠ 0) (ne_of_gt (Real.exp_pos _))]
          rw [show (16:ℝ) = 2^4 from by norm_num, Real.log_pow, Real.log_exp]; ring
        have h2 : 3 * Real.log 3 = Real.log 27 := by
          rw [show (27:ℝ) = 3^3 from by norm_num, Real.log_pow]; ring
        rw [h1, h2]
        apply Real.log_le_log (by positivity)

        have hexp_sq : Real.exp (1/2 : ℝ) ^ 2 = Real.exp 1 := by
          rw [sq, ← Real.exp_add]; norm_num
        nlinarith [sq_nonneg (Real.exp (1/2 : ℝ) - 27/16), Real.exp_pos (1/2 : ℝ),
                   Real.exp_one_lt_d9]
      linarith
    ·
      push Not at hd8
      have hd9 : 9 ≤ d := hd8


      have hlog2 : Real.log 2 ≤ 45 / 64 := by
        rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 2)]
        have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 45/64 by norm_num) 4
        simp [Finset.sum_range_succ] at h; linarith
      have hd_real : (9 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd9

      linarith]

/-- Numerical Fano bound covering both signs of `log(M-1)`:
`1 - (d/64 + log 2)/log(M - 1) ≥ 1/4`. -/
theorem fano_numerical_bound (d M : ℕ) (hd : 0 < d)
    (hM : (M : ℝ) ≥ Real.exp ((1/4 : ℝ) ^ 2 * ↑d / 2))
    (hM4 : 4 ≤ M)
    (hlog_vg : Real.log ((M : ℝ) - 1) ≥ ↑d / 8) :
    (1 : ℝ) - ((↑d / 64 : ℝ) + Real.log 2) / Real.log ((M : ℝ) - 1) ≥ 1 / 4 := by
  by_cases h_log : Real.log ((M : ℝ) - 1) ≤ 0
  ·
    have h_num_pos : (0 : ℝ) < ↑d / 64 + Real.log 2 := by
      have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    by_cases h0 : Real.log ((M : ℝ) - 1) = 0
    · rw [h0, div_zero, sub_zero]; norm_num
    · have h_neg : Real.log ((M : ℝ) - 1) < 0 := lt_of_le_of_ne h_log h0
      have h_div_nonpos : ((↑d / 64 : ℝ) + Real.log 2) / Real.log ((M : ℝ) - 1) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (le_of_lt h_num_pos) (le_of_lt h_neg)
      linarith
  ·
    push Not at h_log
    exact fano_numerical_bound_pos_log d M hd hM hM4 hlog_vg h_log

/-- The local `sqDist` definition agrees with the one from the `InfoTheory` namespace. -/
lemma sqDist_eq_infoTheory_sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) :
    sqDist θ₁ θ₂ = InfoTheory.sqDist θ₁ θ₂ := by
  rfl

/-- The real vector with entry `s` at positions where `ω i = true` and `0` elsewhere. -/
def scaledBoolVec {d : ℕ} (ω : Fin d → Bool) (s : ℝ) : Fin d → ℝ :=
  fun i => if ω i then s else 0

/-- The squared distance between two scaled binary indicators equals `s²` times their
Hamming distance. -/
lemma sqDist_scaledBoolVec {d : ℕ} (ω₁ ω₂ : Fin d → Bool) (s : ℝ) :
    InfoTheory.sqDist (scaledBoolVec ω₁ s) (scaledBoolVec ω₂ s) =
    s ^ 2 * (InfoTheory.hammingDist ω₁ ω₂ : ℝ) := by
  unfold InfoTheory.sqDist scaledBoolVec InfoTheory.hammingDist
  rw [show Finset.card (Finset.filter (fun i => ω₁ i ≠ ω₂ i) Finset.univ) =
    ∑ i : Fin d, if ω₁ i ≠ ω₂ i then 1 else 0 from by
      rw [Finset.card_filter]]
  push_cast [Finset.mul_sum]
  congr 1; ext i
  cases ω₁ i <;> cases ω₂ i <;> simp [sub_self, zero_sub, sq, neg_mul, neg_neg]

/-- Fano-based testing bound: for `d ≥ 2`, there exists a parameter `θ₀` so that the probability
that any measurable estimator's squared error exceeds `σ²d/(512n)` is at least `1/4`. -/
theorem gsm_fano_testing_bound {d : ℕ} (hd : 2 ≤ d)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : IsGSM P σ n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ))
    (hθhat_meas : Measurable θhat) :

    ∃ θ0 : Fin d → ℝ,
      (P θ0 {Y | sqDist (θhat Y) θ0 ≥ σ ^ 2 * ↑d / (512 * ↑n)}).toReal ≥ 1 / 4 := by

  obtain ⟨M, hM_pos, ω, hM_exp, hM_ge4, hlog_M, hω_sep⟩ :=
    InfoTheory.varshamov_gilbert_for_cor513 d hd


  have hM2 : 3 ≤ M := le_trans (by norm_num : 3 ≤ 4) hM_ge4

  let s := σ / (4 * Real.sqrt (2 * ↑n))
  let θ : Fin M → Fin d → ℝ := fun j => scaledBoolVec (ω j) s

  haveI : ∀ j, IsProbabilityMeasure (P (θ j)) :=
    fun j => hP.isProbabilityMeasure hσ hn (θ j)
  haveI : ∀ θ', IsProbabilityMeasure (P θ') :=
    fun θ' => hP.isProbabilityMeasure hσ hn θ'

  have hac : ∀ j k, P (θ j) ≪ P (θ k) :=
    fun j k => gsm_abs_continuous P σ hσ n hn hP (θ j) (θ k)

  have hs_sq : s ^ 2 = σ ^ 2 / (32 * ↑n) := by
    show (σ / (4 * Real.sqrt (2 * ↑n))) ^ 2 = σ ^ 2 / (32 * ↑n)
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : (2 : ℝ) * ↑n ≥ 0)]
    ring

  have hsep : ∀ j k : Fin M, j ≠ k →
      InfoTheory.sqDist (θ j) (θ k) ≥ 4 * (σ ^ 2 * ↑d / (512 * ↑n)) := by
    intro j k hjk
    rw [sqDist_scaledBoolVec, hs_sq]
    have h_sep := hω_sep j k hjk

    rw [ge_iff_le]
    calc 4 * (σ ^ 2 * ↑d / (512 * ↑n))
        = σ ^ 2 / (32 * ↑n) * (↑d / 4) := by ring
      _ ≤ σ ^ 2 / (32 * ↑n) * ↑(InfoTheory.hammingDist (ω j) (ω k)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith


  have hKL_each : ∀ j k : Fin M,
      (klDiv (P (θ j)) (P (θ k))).toReal = ↑n * InfoTheory.sqDist (θ j) (θ k) / (2 * σ ^ 2) := by
    intro j k
    exact InfoTheory.gaussian_kl_divergence (θ j) (θ k) σ hσ n hn P
      (fun θ' i => hP.identity_risk_coord hσ hn θ' i)
      (fun θ₁ θ₂ => hP.density_ratio hσ hn θ₁ θ₂)
      (fun θ' i => hP.coord_mean hσ hn θ' i)


  have hκ : (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M,
      (klDiv (P (θ j)) (P (θ k))).toReal ≤ ↑d / 64 := by

    have hM_pos_real : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
    have hM_sq_pos : (0 : ℝ) < (M : ℝ) ^ 2 := sq_pos_of_pos hM_pos_real

    have hKL_le : ∀ j k : Fin M,
        (klDiv (P (θ j)) (P (θ k))).toReal ≤ ↑d / 64 := by
      intro j k
      rw [hKL_each j k, sqDist_scaledBoolVec, hs_sq]

      have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
      have hσ_sq_pos : (0 : ℝ) < σ ^ 2 := sq_pos_of_pos hσ

      have hham_le_d : (InfoTheory.hammingDist (ω j) (ω k) : ℝ) ≤ ↑d := by
        have : InfoTheory.hammingDist (ω j) (ω k) ≤ d := by
          unfold InfoTheory.hammingDist
          exact (Finset.card_filter_le _ _).trans (Finset.card_fin d).le
        exact_mod_cast this
      rw [show ↑n * (σ ^ 2 / (32 * ↑n) * ↑(InfoTheory.hammingDist (ω j) (ω k))) / (2 * σ ^ 2) =
        ↑(InfoTheory.hammingDist (ω j) (ω k)) / 64 from by field_simp; ring]
      exact div_le_div_of_nonneg_right hham_le_d (by norm_num : (0 : ℝ) ≤ 64)

    have hsum_le : ∑ j : Fin M, ∑ k : Fin M,
        (klDiv (P (θ j)) (P (θ k))).toReal ≤ ↑M ^ 2 * (↑d / 64) := by
      calc ∑ j : Fin M, ∑ k : Fin M, (klDiv (P (θ j)) (P (θ k))).toReal
          ≤ ∑ j : Fin M, ∑ k : Fin M, (↑d / 64 : ℝ) :=
            Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hKL_le j k))
        _ = ↑M * (↑M * (↑d / 64)) := by simp [Finset.sum_const]
        _ = ↑M ^ 2 * (↑d / 64) := by ring

    calc 1 / ↑M ^ 2 * ∑ j : Fin M, ∑ k : Fin M,
          (klDiv (P (θ j)) (P (θ k))).toReal
        ≤ 1 / ↑M ^ 2 * (↑M ^ 2 * (↑d / 64)) :=
          mul_le_mul_of_nonneg_left hsum_le (div_nonneg zero_le_one (sq_nonneg _))
      _ = ↑d / 64 := by field_simp

  have h_fano := InfoTheory.reduction_to_testing_fano hM2 P θ hac
    (fun j k => hP.hP_kl_ne_top (θ k) (θ j))
    (σ ^ 2 * ↑d / (512 * ↑n)) (by positivity) hsep (↑d / 64) hκ θhat hθhat_meas


  have hM4 : 4 ≤ M := hM_ge4
  have hlog_vg : Real.log ((M : ℝ) - 1) ≥ ↑d / 8 := hlog_M

  have hd_pos : 0 < d := by omega
  have h_num := fano_numerical_bound d M hd_pos hM_exp hM4 hlog_vg

  have hne : Nonempty (Fin M) := ⟨⟨0, hM_pos⟩⟩
  have h_spec : ⨆ (j : Fin M), (P (θ j) {Y | InfoTheory.sqDist (θhat Y) (θ j) ≥
      σ ^ 2 * ↑d / (512 * ↑n)}).toReal ≥ 1 / 4 :=
    le_trans h_num h_fano

  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite
    (f := fun j : Fin M => (P (θ j) {Y | InfoTheory.sqDist (θhat Y) (θ j) ≥
      σ ^ 2 * ↑d / (512 * ↑n)}).toReal)

  refine ⟨θ j, ?_⟩


  change (P (θ j) {Y | InfoTheory.sqDist (θhat Y) (θ j) ≥ σ ^ 2 * ↑d / (512 * ↑n)}).toReal ≥ 1 / 4
  linarith [hj]

/-- Two-point Le Cam style testing bound in dimension `d = 1`: there exists `θ₀` such that
no measurable estimator can drive the probability of having squared error below `σ²/(512 n)`
above `3/4`. -/
theorem gsm_two_point_testing_bound
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin 1 → ℝ) → Measure (Fin 1 → ℝ))
    (hP : IsGSM P σ n)
    (θhat : (Fin 1 → ℝ) → (Fin 1 → ℝ))
    (hθhat_meas : Measurable θhat) :
    ∃ θ0 : Fin 1 → ℝ,
      (P θ0 {Y | sqDist (θhat Y) θ0 ≥ σ ^ 2 * (1 : ℝ) / (512 * ↑n)}).toReal ≥ 1 / 4 := by


  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  set ϕ := σ ^ 2 * (1 : ℝ) / (512 * ↑n) with hϕ_def
  have hϕ_pos : 0 < ϕ := by positivity

  set t := σ / Real.sqrt (2 * ↑n)
  have ht_sq : t ^ 2 = σ ^ 2 / (2 * ↑n) := by
    simp only [t, div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * ↑n)]
  set θ₀ : Fin 1 → ℝ := 0
  set θ₁ : Fin 1 → ℝ := fun _ => t

  have hsqd_eq : InfoTheory.sqDist θ₀ θ₁ = σ ^ 2 / (2 * ↑n) := by
    unfold InfoTheory.sqDist
    simp only [θ₀, θ₁, Pi.zero_apply, zero_sub, neg_sq, Finset.univ_unique, Finset.sum_singleton]
    exact ht_sq
  have hsqd_sym : InfoTheory.sqDist θ₁ θ₀ = InfoTheory.sqDist θ₀ θ₁ := by
    simp only [InfoTheory.sqDist]; congr 1; ext i; ring

  have hsqd_ge_4ϕ : InfoTheory.sqDist θ₀ θ₁ ≥ 4 * ϕ := by
    rw [hsqd_eq, hϕ_def, ge_iff_le]
    rw [show 4 * (σ ^ 2 * 1 / (512 * ↑n)) = σ ^ 2 / (128 * ↑n) from by ring]
    exact div_le_div_of_nonneg_left (sq_nonneg σ) (by positivity) (by linarith)

  haveI hP₀_inst := hP.isProbabilityMeasure hσ hn θ₀
  haveI hP₁_inst := hP.isProbabilityMeasure hσ hn θ₁
  haveI : ∀ θ', IsProbabilityMeasure (P θ') :=
    fun θ' => hP.isProbabilityMeasure hσ hn θ'

  have hac := gsm_abs_continuous P σ hσ n hn hP

  have hGSM_kl : ∀ (a b : Fin 1 → ℝ),
      (klDiv (P a) (P b)).toReal = ↑n * InfoTheory.sqDist a b / (2 * σ ^ 2) := by
    intro a b
    exact InfoTheory.gaussian_kl_divergence a b σ hσ n hn P
      (fun θ' i => hP.identity_risk_coord hσ hn θ' i)
      (fun u v => hP.density_ratio hσ hn u v)
      (fun θ' i => hP.coord_mean hσ hn θ' i)

  have hKL_val : (klDiv (P θ₁) (P θ₀)).toReal = 1 / 4 := by
    rw [hGSM_kl, hsqd_sym, hsqd_eq]
    have hσ_ne : σ ≠ 0 := ne_of_gt hσ
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
    field_simp; ring
  have hKL_ne_top : klDiv (P θ₁) (P θ₀) ≠ ⊤ := by
    intro h_top; simp [h_top] at hKL_val

  have hPinsker := @Chapter5.TVNP.pinsker_inequality _ _ (P θ₁) (P θ₀) hP₁_inst hP₀_inst
    (hac θ₁ θ₀) hKL_ne_top
  have hKL_toReal_eq : Chapter5.TVNP.klDiv_real (P θ₁) (P θ₀) = 1 / 4 := by
    unfold Chapter5.TVNP.klDiv_real; rw [hKL_val]
  have hTV_sym : Chapter5.TVNP.tvDist (P θ₀) (P θ₁) =
      Chapter5.TVNP.tvDist (P θ₁) (P θ₀) := by
    unfold Chapter5.TVNP.tvDist
    congr 1; ext x; constructor
    · rintro ⟨S, hS, hx⟩; exact ⟨S, hS, by rw [hx, abs_sub_comm]⟩
    · rintro ⟨S, hS, hx⟩; exact ⟨S, hS, by rw [hx, abs_sub_comm]⟩
  have hTV_bound : Chapter5.TVNP.tvDist (P θ₀) (P θ₁) ≤ 1 / 2 := by
    rw [hTV_sym]
    calc Chapter5.TVNP.tvDist (P θ₁) (P θ₀)
        ≤ Real.sqrt (Chapter5.TVNP.klDiv_real (P θ₁) (P θ₀)) := hPinsker
      _ = Real.sqrt (1 / 4) := by rw [hKL_toReal_eq]
      _ = 1 / 2 := by
          rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 from by norm_num]
          exact Real.sqrt_sq (by norm_num)

  have sqDist_triangle : ∀ a b c : Fin 1 → ℝ,
      InfoTheory.sqDist a b ≤ 2 * InfoTheory.sqDist c a + 2 * InfoTheory.sqDist c b := by
    intro a b c
    show ∑ i, (a i - b i) ^ 2 ≤ 2 * ∑ i, (c i - a i) ^ 2 + 2 * ∑ i, (c i - b i) ^ 2
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (a i - c i + c i - b i), sq_nonneg (a i - c i - (c i - b i))]

  have hE₀_meas : MeasurableSet {Y : Fin 1 → ℝ | InfoTheory.sqDist (θhat Y) θ₀ ≥ ϕ} := by
    unfold InfoTheory.sqDist
    apply measurableSet_le measurable_const
    apply Finset.measurable_sum; intro i _
    exact ((measurable_pi_apply i |>.comp hθhat_meas).sub measurable_const).pow measurable_const

  let ψ : (Fin 1 → ℝ) → Bool := fun Y => decide (InfoTheory.sqDist (θhat Y) θ₀ ≥ ϕ)
  have hψ_meas : Measurable ψ := by
    apply measurable_to_countable'; intro b; cases b
    · convert hE₀_meas.compl using 1
      ext Y; simp [ψ, decide_eq_false_iff_not, not_le]
    · convert hE₀_meas using 1; ext Y; simp [ψ, decide_eq_true_eq]

  have hNP := Chapter5.TVNP.neyman_pearson_lower (P θ₀) (P θ₁) hP₀_inst hP₁_inst ψ hψ_meas
  have hψ_true : {Y | ψ Y = true} = {Y | InfoTheory.sqDist (θhat Y) θ₀ ≥ ϕ} := by
    ext Y; simp [ψ, decide_eq_true_eq]

  have h_incl : {Y | ψ Y = false} ⊆ {Y | InfoTheory.sqDist (θhat Y) θ₁ ≥ ϕ} := by
    intro Y hY
    simp only [Set.mem_setOf_eq, ψ, decide_eq_false_iff_not, not_le] at hY
    simp only [Set.mem_setOf_eq]
    have htri := sqDist_triangle θ₀ θ₁ (θhat Y)
    linarith [hsqd_ge_4ϕ]
  have h_mono : (P θ₁ {Y | ψ Y = false}).toReal ≤
      (P θ₁ {Y | InfoTheory.sqDist (θhat Y) θ₁ ≥ ϕ}).toReal :=
    ENNReal.toReal_mono (measure_ne_top (P θ₁) _) (measure_mono h_incl)
  rw [hψ_true] at hNP

  set E₀ := {Y | InfoTheory.sqDist (θhat Y) θ₀ ≥ ϕ}
  set E₁ := {Y | InfoTheory.sqDist (θhat Y) θ₁ ≥ ϕ}
  have hsum : (P θ₀ E₀).toReal + (P θ₁ E₁).toReal ≥ 1 / 2 := by
    linarith


  have hsets_eq₀ : {Y | sqDist (θhat Y) θ₀ ≥ σ ^ 2 * 1 / (512 * ↑n)} = E₀ := by
    ext Y; simp only [Set.mem_setOf_eq, E₀, sqDist, InfoTheory.sqDist, hϕ_def]
  have hsets_eq₁ : {Y | sqDist (θhat Y) θ₁ ≥ σ ^ 2 * 1 / (512 * ↑n)} = E₁ := by
    ext Y; simp only [Set.mem_setOf_eq, E₁, sqDist, InfoTheory.sqDist, hϕ_def]

  have hP₀_nn : 0 ≤ (P θ₀ E₀).toReal := ENNReal.toReal_nonneg
  have hP₁_nn : 0 ≤ (P θ₁ E₁).toReal := ENNReal.toReal_nonneg
  by_cases h : (P θ₀ E₀).toReal ≥ 1 / 4
  · exact ⟨θ₀, by rw [hsets_eq₀]; exact h⟩
  · push Not at h
    have : (P θ₁ E₁).toReal ≥ 1 / 4 := by linarith
    exact ⟨θ₁, by rw [hsets_eq₁]; exact this⟩

/-- Witness lower bound for `d ≥ 2`: any measurable estimator has supremum risk at least
`σ² d / (2048 n)`. -/
theorem fano_witness_positive_d_ge_2 {d : ℕ} (hd : 2 ≤ d)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : IsGSM P σ n)
    (θhat : Estimator d)
    (hθhat_meas : Measurable θhat) :
    supRisk P Set.univ θhat ≥ 1 / 2048 * σ ^ 2 * ↑d / ↑n := by

  obtain ⟨θ0, hθ0_prob⟩ := gsm_fano_testing_bound hd σ hσ n hn P hP θhat hθhat_meas


  have h_ϕ_pos : (0 : ℝ) < σ ^ 2 * ↑d / (512 * ↑n) := by positivity
  have h_risk_bound : 1 / 4 * (σ ^ 2 * ↑d / (512 * ↑n)) ≤
      ∫ Y, sqDist (θhat Y) θ0 ∂(P θ0) := by


    have h_nonneg : ∀ Y, sqDist (θhat Y) θ0 ≥ 0 := fun Y => by
      unfold sqDist; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h_int := gsm_integrable_sqDist P σ hσ n hn hP θhat θ0
    exact InfoTheory.markov_step (P θ0) (fun Y => sqDist (θhat Y) θ0)
      (σ ^ 2 * ↑d / (512 * ↑n)) (1 / 4)
      h_ϕ_pos (by norm_num) h_nonneg h_int hθ0_prob


  unfold supRisk
  rw [ge_iff_le]
  calc 1 / 2048 * σ ^ 2 * ↑d / ↑n
      = 1 / 4 * (σ ^ 2 * ↑d / (512 * ↑n)) := by ring
    _ ≤ ∫ Y, sqDist (θhat Y) θ0 ∂(P θ0) := h_risk_bound
    _ = risk P θhat θ0 := by unfold risk; rfl
    _ ≤ ⨆ θ, ⨆ (_ : θ ∈ Set.univ), risk P θhat θ := by
        apply le_ciSup_of_le (gsm_bddAbove_risk P σ hσ n hn hP θhat) θ0
        exact le_ciSup ⟨risk P θhat θ0, by rintro _ ⟨_, rfl⟩; rfl⟩ (Set.mem_univ θ0)

/-- Witness lower bound for `d ≥ 1`: any measurable estimator has supremum risk at least
`σ² d / (2048 n)`. -/
theorem fano_witness_positive {d : ℕ} (hd : 1 ≤ d)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : IsGSM P σ n)
    (θhat : Estimator d)
    (hθhat_meas : Measurable θhat) :
    supRisk P Set.univ θhat ≥ 1 / 2048 * σ ^ 2 * ↑d / ↑n := by
  by_cases hd2 : 2 ≤ d
  · exact fano_witness_positive_d_ge_2 hd2 σ hσ n hn P hP θhat hθhat_meas
  ·
    have hd1 : d = 1 := by omega
    subst hd1

    obtain ⟨θ0, hθ0_prob⟩ := gsm_two_point_testing_bound σ hσ n hn P hP θhat hθhat_meas

    have h_ϕ_pos : (0 : ℝ) < σ ^ 2 * (1 : ℝ) / (512 * ↑n) := by positivity
    have h_risk_bound : 1 / 4 * (σ ^ 2 * (1 : ℝ) / (512 * ↑n)) ≤
        ∫ Y, sqDist (θhat Y) θ0 ∂(P θ0) := by
      have h_nonneg : ∀ Y, sqDist (θhat Y) θ0 ≥ 0 := fun Y => by
        unfold sqDist; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have h_int := gsm_integrable_sqDist P σ hσ n hn hP θhat θ0
      exact InfoTheory.markov_step (P θ0) (fun Y => sqDist (θhat Y) θ0)
        (σ ^ 2 * 1 / (512 * ↑n)) (1 / 4)
        h_ϕ_pos (by norm_num) h_nonneg h_int hθ0_prob
    unfold supRisk
    rw [ge_iff_le]
    calc 1 / 2048 * σ ^ 2 * ↑(1 : ℕ) / ↑n
        = 1 / 4 * (σ ^ 2 * (1 : ℝ) / (512 * ↑n)) := by push_cast; ring
      _ ≤ ∫ Y, sqDist (θhat Y) θ0 ∂(P θ0) := h_risk_bound
      _ = risk P θhat θ0 := by unfold risk; rfl
      _ ≤ ⨆ θ, ⨆ (_ : θ ∈ Set.univ), risk P θhat θ := by
          apply le_ciSup_of_le (gsm_bddAbove_risk P σ hσ n hn hP θhat) θ0
          exact le_ciSup ⟨risk P θhat θ0, by rintro _ ⟨_, rfl⟩; rfl⟩ (Set.mem_univ θ0)

/-- Minimax lower bound `φ(ℝ^d) ≥ C σ² d / n` for some explicit constant `C > 0`. -/
theorem minimax_lower_bound
    {d : ℕ} (hd : 1 ≤ d)
    (σ : ℝ) (hσ : 0 < σ)
    (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : IsGSM P σ n) :
    ∃ C : ℝ, 0 < C ∧
      minimaxRisk P (Set.univ : Set (Fin d → ℝ)) ≥ C * σ ^ 2 * ↑d / ↑n := by

  refine ⟨1 / 2048, by norm_num, ?_⟩


  unfold minimaxRisk
  rw [ge_iff_le]
  haveI : Nonempty { f : Estimator d // Measurable f } :=
    ⟨⟨id, measurable_id⟩⟩
  apply le_ciInf
  rintro ⟨θhat, hmeas⟩

  have h := fano_witness_positive hd σ hσ n hn P hP θhat hmeas
  unfold supRisk risk at h ⊢
  exact h

/-- The identity (least squares) estimator achieves risk exactly `σ² d / n` at every parameter
in the Gaussian sequence model. -/
theorem identity_estimator_risk
    {d : ℕ} (hd : 0 < d)
    (σ : ℝ) (hσ : 0 < σ)
    (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : IsGSM P σ n) :
    ∀ θ : Fin d → ℝ,
      risk P (identityEstimator d) θ = σ ^ 2 * ↑d / ↑n := by
  intro θ
  unfold risk identityEstimator sqDist
  simp only [id_eq]
  have hint : ∀ i : Fin d, Integrable (fun Y => (Y i - θ i) ^ 2) (P θ) := by
    intro i
    by_contra hni
    have h := hP.identity_risk_coord hσ hn θ i
    simp [integral_undef hni] at h
    linarith [div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr hn)]
  rw [integral_finset_sum Finset.univ (fun i _ => hint i)]
  simp only [Finset.sum_congr rfl (fun i _ => hP.identity_risk_coord hσ hn θ i)]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Corollary 5.13** (minimax rate over `ℝ^d`): the minimax rate of estimation in the Gaussian
sequence model on `ℝ^d` is `φ(ℝ^d) = σ² d / n`, matched up to constants by a Fano lower bound
and attained exactly by the least squares (identity) estimator `θ̂^{LS} = Y`. -/
theorem minimax_rate
    {d : ℕ} (hd : 1 ≤ d)
    (σ : ℝ) (hσ : 0 < σ)
    (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : IsGSM P σ n) :

    (∃ C' : ℝ, 0 < C' ∧
      minimaxRisk P (Set.univ : Set (Fin d → ℝ)) ≥ C' * σ ^ 2 * ↑d / ↑n) ∧

    minimaxRisk P (Set.univ : Set (Fin d → ℝ)) ≤ σ ^ 2 * ↑d / ↑n ∧

    supRisk P (Set.univ : Set (Fin d → ℝ)) (identityEstimator d) = σ ^ 2 * ↑d / ↑n := by
  have hd_pos : 0 < d := by omega

  have hc : supRisk P (Set.univ : Set (Fin d → ℝ)) (identityEstimator d) = σ ^ 2 * ↑d / ↑n := by
    unfold supRisk
    simp_rw [identity_estimator_risk hd_pos σ hσ n hn P hP]
    simp [Set.mem_univ, ciSup_const]

  have hb : minimaxRisk P (Set.univ : Set (Fin d → ℝ)) ≤ σ ^ 2 * ↑d / ↑n := by
    rw [← hc]
    show minimaxRisk P Set.univ ≤ supRisk P Set.univ (identityEstimator d)
    have hid_meas : Measurable (identityEstimator d) := measurable_id
    have hbdd : BddBelow (Set.range fun (θhat : { f : Estimator d // Measurable f }) =>
        supRisk P Set.univ θhat.val) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨⟨θhat, hmeas⟩, rfl⟩
      unfold supRisk
      apply le_ciSup_of_le (hP.bddAbove_risk hσ hn θhat) (0 : Fin d → ℝ)
      simp only [Set.mem_univ, ciSup_const]
      exact integral_nonneg (fun Y => Finset.sum_nonneg (fun i _ => sq_nonneg _))
    exact ciInf_le hbdd ⟨identityEstimator d, hid_meas⟩
  exact ⟨minimax_lower_bound hd σ hσ n hn P hP, hb, hc⟩

end GaussianSequenceModel


namespace Cor_5_13

export GaussianSequenceModel (sqDist Estimator identityEstimator risk supRisk minimaxRisk l1norm
  IsGSM oracle_ineq_pointwise gsm_abs_continuous gsm_integrable_sqDist gsm_measurable_sqDist
  gsm_bddAbove_risk fano_numerical_bound_pos_log fano_numerical_bound sqDist_eq_infoTheory_sqDist
  scaledBoolVec sqDist_scaledBoolVec gsm_fano_testing_bound gsm_two_point_testing_bound
  fano_witness_positive_d_ge_2 fano_witness_positive minimax_lower_bound identity_estimator_risk
  minimax_rate)

end Cor_5_13

end
