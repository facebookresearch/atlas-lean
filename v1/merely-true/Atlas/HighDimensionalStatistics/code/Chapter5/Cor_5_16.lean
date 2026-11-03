/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Card
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_13
import Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_15

open Real MeasureTheory InformationTheory

noncomputable section

namespace MinimaxL1Ball

/-- The `ℓ¹`-norm `|θ|_1 = ∑_i |θ_i|`. -/
def l1norm {d : ℕ} (θ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, |θ i|

/-- The `ℓ¹`-ball of radius `R`: vectors with `|θ|_1 ≤ R`. -/
def l1Ball (d : ℕ) (R : ℝ) : Set (Fin d → ℝ) :=
  {θ | l1norm θ ≤ R}

/-- Squared Euclidean distance between two vectors in `ℝ^d`. -/
def sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (θ₁ i - θ₂ i) ^ 2

/-- A (not-necessarily measurable) estimator `ℝ^d → ℝ^d`. -/
def Estimator' (d : ℕ) := (Fin d → ℝ) → (Fin d → ℝ)

/-- `Estimator' d` is nonempty (witnessed by the identity). -/
instance {d : ℕ} : Nonempty (Estimator' d) := ⟨id⟩

/-- Subtype of measurable estimators `ℝ^d → ℝ^d`. -/
def MeasEstimator (d : ℕ) := { θhat : (Fin d → ℝ) → (Fin d → ℝ) // Measurable θhat }

/-- `MeasEstimator d` is nonempty (witnessed by the constant-zero estimator). -/
instance {d : ℕ} : Nonempty (MeasEstimator d) := ⟨⟨fun _ => 0, measurable_const⟩⟩

/-- The minimax expected risk over the `ℓ¹`-ball `B₁(R)`: infimum over measurable estimators of
the worst-case expected squared error over `θ ∈ B₁(R)`. -/
noncomputable def minimaxExpRisk_l1 {d : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ)) (R : ℝ) : ℝ :=
  ⨅ (θhat : MeasEstimator d),
    ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (θhat.1 Y) θ ∂(P θ)

open Classical in
/-- The constrained least squares estimator over the `ℓ¹`-ball `B₁(R)`; returns `0` if no
minimizer exists. -/
noncomputable def constrainedLSEstimator (d : ℕ) (R : ℝ) : Estimator' d :=
  fun Y => if h : ∃ θ ∈ l1Ball d R, ∀ θ' ∈ l1Ball d R, sqDist Y θ ≤ sqDist Y θ'
            then h.choose else fun _ => 0

/-- The trivial estimator `θ̂(Y) ≡ 0`. -/
def trivialEstimator (d : ℕ) : Estimator' d := fun _ => fun _ => 0

/-- The trivial estimator is measurable. -/
lemma measurable_trivialEstimator (d : ℕ) : Measurable (trivialEstimator d) :=
  measurable_const

/-- The trivial estimator bundled with its measurability proof. -/
def trivialMeasEstimator (d : ℕ) : MeasEstimator d :=
  ⟨trivialEstimator d, measurable_trivialEstimator d⟩

open Finset Filter Topology in
/-- The `ℓ¹`-ball `B₁(R)` in `ℝ^d` is compact. -/
lemma isCompact_l1Ball (d : ℕ) (R : ℝ) : IsCompact (l1Ball d R) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le
      (continuous_finset_sum _ fun i _ => continuous_abs.comp (continuous_apply i))
      continuous_const
  · rw [Metric.isBounded_iff_subset_ball 0]
    refine ⟨max R 0 + 1, fun θ hθ => ?_⟩
    simp only [Metric.mem_ball, dist_zero_right, l1Ball, Set.mem_setOf_eq, l1norm] at *
    rw [pi_norm_lt_iff (by linarith [le_max_right R 0])]
    intro i
    have h1 : |θ i| ≤ ∑ j, |θ j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (θ j)) (Finset.mem_univ i)
    calc ‖θ i‖ = |θ i| := Real.norm_eq_abs _
      _ ≤ R := le_trans h1 hθ
      _ ≤ max R 0 := le_max_left R 0
      _ < max R 0 + 1 := lt_add_one _

open Finset in
/-- The `ℓ¹`-ball `B₁(R)` is convex. -/
lemma convex_l1Ball (d : ℕ) (R : ℝ) : Convex ℝ (l1Ball d R) := by
  intro x hx y hy a b ha hb hab
  simp only [l1Ball, Set.mem_setOf_eq, l1norm] at *
  calc ∑ i, |a * x i + b * y i|
      ≤ ∑ i, (a * |x i| + b * |y i|) :=
        Finset.sum_le_sum fun i _ => (abs_add_le _ _).trans
          (by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb])
    _ = a * ∑ i, |x i| + b * ∑ i, |y i| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * R + b * R :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = R := by rw [← add_mul, hab, one_mul]

open Finset in
/-- Parallelogram-style identity: `‖Y - (θ₁ + θ₂)/2‖² = (‖Y - θ₁‖² + ‖Y - θ₂‖²)/2 - ‖θ₁ - θ₂‖²/4`. -/
lemma midpoint_sqDist {d : ℕ} (Y θ₁ θ₂ : Fin d → ℝ) :
    sqDist Y (fun i => (θ₁ i + θ₂ i) / 2) =
    (sqDist Y θ₁ + sqDist Y θ₂) / 2 - sqDist θ₁ θ₂ / 4 := by
  simp only [sqDist]
  simp_rw [show ∀ i : Fin d,
      (Y i - (θ₁ i + θ₂ i) / 2) ^ 2 =
      ((Y i - θ₁ i) ^ 2 + (Y i - θ₂ i) ^ 2) / 2 - (θ₁ i - θ₂ i) ^ 2 / 4
    from fun i => by ring,
    Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_add_distrib]

open Finset in
/-- If `θ₁ ≠ θ₂`, then `sqDist θ₁ θ₂ > 0`. -/
lemma sqDist_pos_of_ne {d : ℕ} {θ₁ θ₂ : Fin d → ℝ} (h : θ₁ ≠ θ₂) :
    0 < sqDist θ₁ θ₂ := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, θ₁ i ≠ θ₂ i := by
    by_contra hall; push Not at hall; exact h (funext hall)
  exact Finset.sum_pos' (fun i _ => sq_nonneg _)
    ⟨i₀, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hi₀)⟩

/-- Two squared-distance minimizers of `Y` over a convex set `S` must coincide. -/
lemma unique_minimizer_sqDist {d : ℕ} (Y : Fin d → ℝ)
    {S : Set (Fin d → ℝ)} (hconv : Convex ℝ S)
    {θ₁ θ₂ : Fin d → ℝ} (h1 : θ₁ ∈ S) (h2 : θ₂ ∈ S)
    (hmin1 : ∀ θ' ∈ S, sqDist Y θ₁ ≤ sqDist Y θ')
    (hmin2 : ∀ θ' ∈ S, sqDist Y θ₂ ≤ sqDist Y θ') : θ₁ = θ₂ := by
  by_contra h
  let mid := fun i => (θ₁ i + θ₂ i) / 2
  have hmid : mid ∈ S := by
    have : mid = (1/2 : ℝ) • θ₁ + (1/2 : ℝ) • θ₂ := by ext i; simp [mid]; ring
    rw [this]; exact hconv h1 h2 (by norm_num) (by norm_num) (by norm_num)
  linarith [sqDist_pos_of_ne h, midpoint_sqDist Y θ₁ θ₂, hmin1 mid hmid, hmin2 mid hmid]

open Finset Filter Topology in
/-- Continuity of `sqDist` for sequences: if `Ys → Y` and `θs → θ`, then `sqDist(Ys, θs) → sqDist(Y, θ)`. -/
lemma tendsto_sqDist_of_tendsto {d : ℕ}
    {Ys : ℕ → Fin d → ℝ} {Y : Fin d → ℝ} (hY : Tendsto Ys atTop (𝓝 Y))
    {θs : ℕ → Fin d → ℝ} {θ : Fin d → ℝ} (hθ : Tendsto θs atTop (𝓝 θ)) :
    Tendsto (fun n => sqDist (Ys n) (θs n)) atTop (𝓝 (sqDist Y θ)) := by
  apply tendsto_finset_sum; intro i _
  exact ((continuous_apply i).continuousAt.tendsto.comp hY |>.sub
         ((continuous_apply i).continuousAt.tendsto.comp hθ)).pow 2

open Filter Topology in
/-- Limits of squared-distance minimizers remain minimizers. -/
lemma limit_is_minimizer_sqDist {d : ℕ} {S : Set (Fin d → ℝ)}
    {Ys : ℕ → Fin d → ℝ} {Y : Fin d → ℝ} (hY : Tendsto Ys atTop (𝓝 Y))
    {θs : ℕ → Fin d → ℝ} {θ : Fin d → ℝ} (hθ : Tendsto θs atTop (𝓝 θ))
    (hmin : ∀ n, ∀ θ' ∈ S, sqDist (Ys n) (θs n) ≤ sqDist (Ys n) θ')
    (θ' : Fin d → ℝ) (hθ' : θ' ∈ S) : sqDist Y θ ≤ sqDist Y θ' :=
  le_of_tendsto_of_tendsto
    (tendsto_sqDist_of_tendsto hY hθ)
    (tendsto_sqDist_of_tendsto hY tendsto_const_nhds)
    (Eventually.of_forall fun n => hmin n θ' hθ')

/-- The constrained `ℓ¹`-ball least squares estimator is a continuous function of the data. -/
theorem continuous_constrainedLSEstimator (d : ℕ) (R : ℝ) :
    Continuous (constrainedLSEstimator d R) := by
  open Finset Filter Topology Classical in
  by_cases hR : R < 0
  ·
    have hempty : ∀ θ : Fin d → ℝ, θ ∉ l1Ball d R := by
      intro θ hθ
      have : 0 ≤ l1norm θ := Finset.sum_nonneg (fun i _ => abs_nonneg (θ i))
      simp only [l1Ball, Set.mem_setOf_eq] at hθ
      linarith
    have hconst : constrainedLSEstimator d R = fun _ => fun _ => 0 := by
      funext Y
      simp only [constrainedLSEstimator]
      have : ¬∃ θ ∈ l1Ball d R, ∀ θ' ∈ l1Ball d R, sqDist Y θ ≤ sqDist Y θ' := by
        intro ⟨θ, hθ, _⟩; exact hempty θ hθ
      simp [dif_neg this]
    rw [hconst]; exact continuous_const
  ·
    push Not at hR
    rw [continuous_iff_seqContinuous]
    intro Ys Y hYs

    have hexists : ∀ Z : Fin d → ℝ,
        ∃ θ ∈ l1Ball d R, ∀ θ' ∈ l1Ball d R, sqDist Z θ ≤ sqDist Z θ' := by
      intro Z
      have hne : (l1Ball d R).Nonempty := ⟨0, by simp [l1Ball, l1norm, hR]⟩
      have hcont : ContinuousOn (sqDist Z) (l1Ball d R) :=
        (continuous_finset_sum _ fun i _ =>
          (continuous_const.sub (continuous_apply i)).pow 2).continuousOn
      obtain ⟨θ, hθm, hθmin⟩ := (isCompact_l1Ball d R).exists_isMinOn hne hcont
      exact ⟨θ, hθm, fun θ' hθ' => hθmin hθ'⟩

    have hval : ∀ Z : Fin d → ℝ,
        constrainedLSEstimator d R Z ∈ l1Ball d R ∧
        ∀ θ' ∈ l1Ball d R, sqDist Z (constrainedLSEstimator d R Z) ≤ sqDist Z θ' := by
      intro Z
      have h := hexists Z
      have : constrainedLSEstimator d R Z = h.choose := by
        simp only [constrainedLSEstimator]; rw [dif_pos h]
      rw [this]
      exact h.choose_spec


    apply tendsto_of_subseq_tendsto
    intro ns hns

    have hmem : ∀ n, constrainedLSEstimator d R (Ys (ns n)) ∈ l1Ball d R :=
      fun n => (hval (Ys (ns n))).1

    obtain ⟨θlim, hθlim_mem, φ, hφ_mono, hφ_tendsto⟩ :=
      (isCompact_l1Ball d R).isSeqCompact hmem

    have hYsub : Tendsto (fun n => Ys (ns (φ n))) atTop (𝓝 Y) :=
      hYs.comp (hns.comp hφ_mono.tendsto_atTop)

    have hθlim_min : ∀ θ' ∈ l1Ball d R, sqDist Y θlim ≤ sqDist Y θ' := by
      intro θ' hθ'
      apply limit_is_minimizer_sqDist hYsub hφ_tendsto
      · intro n; exact (hval (Ys (ns (φ n)))).2
      · exact hθ'


    have heq : θlim = constrainedLSEstimator d R Y :=
      unique_minimizer_sqDist Y (convex_l1Ball d R)
        hθlim_mem (hval Y).1 hθlim_min (hval Y).2

    exact ⟨φ, heq ▸ hφ_tendsto⟩

/-- Measurability of the constrained `ℓ¹`-ball least squares estimator. -/
theorem measurable_constrainedLSEstimator (d : ℕ) (R : ℝ) :
    Measurable (constrainedLSEstimator d R) :=
  (continuous_constrainedLSEstimator d R).measurable

/-- The constrained LS estimator bundled with its measurability proof. -/
noncomputable def constrainedLSMeasEstimator (d : ℕ) (R : ℝ) : MeasEstimator d :=
  ⟨constrainedLSEstimator d R, measurable_constrainedLSEstimator d R⟩

/-- Squared distance from the trivial estimator's output to `θ` equals `∑_i θ_i²`. -/
lemma sqDist_trivialEstimator {d : ℕ} (Y θ : Fin d → ℝ) :
    sqDist (trivialEstimator d Y) θ = ∑ i : Fin d, (θ i) ^ 2 := by
  simp [sqDist, trivialEstimator, zero_sub]

/-- `∑_i θ_i² ≤ (∑_i |θ_i|)² = |θ|_1²`. -/
lemma sum_sq_le_l1norm_sq {d : ℕ} (θ : Fin d → ℝ) :
    ∑ i : Fin d, (θ i) ^ 2 ≤ l1norm θ ^ 2 := by
  simp_rw [(sq_abs (θ _)).symm]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)

/-- For `θ ∈ B₁(R)`, the squared `ℓ²`-norm `∑_i θ_i²` is bounded by `R²`. -/
lemma sum_sq_le_R_sq_of_l1Ball {d : ℕ} {R : ℝ} (hR : 0 < R)
    (θ : Fin d → ℝ) (hθ : θ ∈ l1Ball d R) :
    ∑ i : Fin d, (θ i) ^ 2 ≤ R ^ 2 := by
  calc ∑ i, (θ i) ^ 2 ≤ l1norm θ ^ 2 := sum_sq_le_l1norm_sq θ
    _ ≤ R ^ 2 := by
        apply sq_le_sq'
        · linarith [show (0 : ℝ) ≤ l1norm θ from
            Finset.sum_nonneg (fun i _ => abs_nonneg (θ i))]
        · exact hθ

/-- In the small-radius regime `R < σ log d / n`, the trivial estimator `θ̂ ≡ 0` achieves
worst-case risk at most `2 · min(R², R σ log d / n)`. -/
lemma trivialEstimator_attains {d : ℕ} (σ R : ℝ) (hσ : 0 < σ) (hR : 0 < R)
    (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : Cor_5_13.IsGSM P σ n)
    (hR_small : R < σ * Real.log ↑d / ↑n) :
    ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (trivialEstimator d Y) θ ∂(P θ) ≤
      2 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n) := by

  have h_int : ∀ θ : Fin d → ℝ,
      ∫ Y, sqDist (trivialEstimator d Y) θ ∂(P θ) = ∑ i : Fin d, (θ i) ^ 2 := by
    intro θ
    simp_rw [sqDist_trivialEstimator]
    haveI := hP.isProbabilityMeasure hσ hn θ
    simp [integral_const]

  have h_bound : ⨆ θ ∈ l1Ball d R,
      ∫ Y, sqDist (trivialEstimator d Y) θ ∂(P θ) ≤ R ^ 2 := by
    simp_rw [h_int]
    apply ciSup_le
    intro θ
    by_cases hθ : θ ∈ l1Ball d R
    · haveI : Nonempty (θ ∈ l1Ball d R) := ⟨hθ⟩
      rw [ciSup_const]
      exact sum_sq_le_R_sq_of_l1Ball hR θ hθ
    · have inst : IsEmpty (θ ∈ l1Ball d R) := isEmpty_Prop.mpr hθ
      rw [@Real.iSup_of_isEmpty _ inst]
      positivity


  have h_min_eq : min (R ^ 2) (R * σ * Real.log ↑d / ↑n) = R ^ 2 := by
    apply min_eq_left
    calc R ^ 2 = R * R := by ring
      _ ≤ R * (σ * Real.log ↑d / ↑n) :=
          mul_le_mul_of_nonneg_left (le_of_lt hR_small) (le_of_lt hR)
      _ = R * σ * Real.log ↑d / ↑n := by ring

  calc ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (trivialEstimator d Y) θ ∂(P θ)
      ≤ R ^ 2 := h_bound
    _ ≤ 2 * R ^ 2 := by linarith [sq_nonneg R]
    _ = 2 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n) := by rw [h_min_eq]

/-- The `ℓ¹`-norm of `scaledBoolVec ω s` equals `s · |ω|_0` when `s ≥ 0`. -/
lemma l1norm_scaledBoolVec {d : ℕ} (ω : Fin d → Bool) (s : ℝ) (hs : 0 ≤ s) :
    l1norm (Cor_5_13.scaledBoolVec ω s) = s * ↑(InfoTheory.l0norm_bool ω) := by
  unfold l1norm Cor_5_13.scaledBoolVec InfoTheory.l0norm_bool
  rw [show Finset.card (Finset.filter (fun i => ω i = true) Finset.univ) =
    ∑ i : Fin d, if ω i = true then 1 else 0 from by rw [Finset.card_filter]]
  push_cast [Finset.mul_sum]
  congr 1; ext i
  cases ω i <;> simp [abs_of_nonneg hs]

/-- A `k`-sparse binary vector scaled by `R/k` lies in the `ℓ¹`-ball `B₁(R)`. -/
lemma scaledBoolVec_in_l1Ball {d : ℕ} (ω : Fin d → Bool) (R : ℝ) (k : ℕ)
    (hR : 0 < R) (hk : 0 < k) (hweight : InfoTheory.l0norm_bool ω = k) :
    Cor_5_13.scaledBoolVec ω (R / ↑k) ∈ l1Ball d R := by
  unfold l1Ball
  simp only [Set.mem_setOf_eq]
  rw [l1norm_scaledBoolVec _ _ (le_of_lt (div_pos hR (Nat.cast_pos.mpr hk)))]
  rw [hweight]
  rw [div_mul_cancel₀]
  exact ne_of_gt (Nat.cast_pos.mpr hk)

/-- Numerical Fano bound: if `M ≥ 5` and `κ ≤ (1/8) log(M-1)`, then
`1 - (κ + log 2) / log(M-1) ≥ 1/4`. -/
theorem l1Ball_fano_numerical_bound (κ : ℝ) (M : ℕ) (hM5 : 5 ≤ M)
    (hκ_bound : κ ≤ (1 / 8) * Real.log ((M : ℝ) - 1)) :
    (1 : ℝ) - (κ + Real.log 2) / Real.log ((M : ℝ) - 1) ≥ 1 / 4 := by
  have hM_ge : (5 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM5
  have hlog_pos : 0 < Real.log ((M : ℝ) - 1) := by
    apply Real.log_pos; linarith
  suffices h : (κ + Real.log 2) / Real.log ((M : ℝ) - 1) ≤ 3 / 4 by linarith
  rw [div_le_iff₀ hlog_pos]
  have hlog4 : Real.log 4 ≤ Real.log ((M : ℝ) - 1) := by
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 4); linarith
  have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; ring
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [hlog4_eq, hlog4, hlog2_pos, hlog_pos]

/-- KL divergence between two GSM laws indexed by scaled binary indicators equals
`n · s² · hammingDist(ωⱼ, ωₖ) / (2σ²)`. -/
lemma gsm_kl_scaledBoolVec {d M : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (hP : Cor_5_13.IsGSM P σ n)
    (ω : Fin M → (Fin d → Bool)) (s : ℝ)
    (j k : Fin M) :
    (klDiv (P (Cor_5_13.scaledBoolVec (ω j) s))
           (P (Cor_5_13.scaledBoolVec (ω k) s))).toReal =
    ↑n * (s ^ 2 * ↑(InfoTheory.hammingDist (ω j) (ω k))) / (2 * σ ^ 2) := by
  haveI : ∀ θ, IsProbabilityMeasure (P θ) :=
    fun θ => hP.isProbabilityMeasure hσ hn θ
  rw [InfoTheory.gaussian_kl_divergence _ _ σ hσ n hn P
    (fun θ' i => hP.identity_risk_coord hσ hn θ' i)
    (fun θ₁ θ₂ => hP.density_ratio hσ hn θ₁ θ₂)
    (fun θ' i => hP.coord_mean hσ hn θ' i)]
  congr 1
  rw [Cor_5_13.sqDist_scaledBoolVec]

/-- For `M ≥ 5`, `log(M-1) ≥ (1/2) log M`. -/
lemma log_sub_one_ge_half_log {M : ℕ} (hM : 5 ≤ M) :
    Real.log ((M : ℝ) - 1) ≥ (1 / 2) * Real.log (M : ℝ) := by
  have hM_ge5 : (5 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM_pos : (0 : ℝ) < M := by linarith
  rw [ge_iff_le, ← Real.log_rpow hM_pos]
  apply Real.log_le_log (Real.rpow_pos_of_pos hM_pos _)
  rw [show (M : ℝ) ^ ((1:ℝ)/2) = Real.sqrt M from by rw [Real.sqrt_eq_rpow]]
  rw [← Real.sqrt_sq (by linarith : (0:ℝ) ≤ (M:ℝ) - 1)]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((M:ℝ) - 1)])

/-- Converts the `k²`-style KL bound from the Varshamov-Gilbert code into the form needed by
the Fano numerical bound. -/
lemma kl_bound_from_k_squared {d k : ℕ} {n : ℕ} {σ R : ℝ}
    (hk1 : 1 ≤ k) (hσ : 0 < σ)
    (h_ineq : 128 * ↑n * R ^ 2 / σ ^ 2 ≤
      (k : ℝ) ^ 2 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ))))
    {M : ℕ} (hM5 : 5 ≤ M)
    (hlogM : Real.log (M : ℝ) ≥
      (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ)))) :
    ↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) ≤ (1 / 8) * Real.log ((M : ℝ) - 1) := by
  have h1 := log_sub_one_ge_half_log hM5
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hσ2_pos : (0 : ℝ) < σ ^ 2 := sq_pos_of_pos hσ
  have h_step1 : ↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) ≤
      (k : ℝ) / 128 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ))) := by
    rw [div_le_iff₀ (mul_pos hk_pos hσ2_pos)]
    have h' : 128 * ↑n * R ^ 2 ≤
        (k : ℝ) ^ 2 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ))) * σ ^ 2 := by
      rw [div_le_iff₀ hσ2_pos] at h_ineq; linarith
    nlinarith [sq_nonneg (k : ℝ)]
  calc ↑n * R ^ 2 / ((k : ℝ) * σ ^ 2)
      ≤ (k : ℝ) / 128 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ))) := h_step1
    _ = (1 / 16) * ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ)))) := by ring
    _ ≤ (1 / 16) * Real.log (M : ℝ) := by linarith [hlogM]
    _ = (1 / 8) * ((1 / 2) * Real.log (M : ℝ)) := by ring
    _ ≤ (1 / 8) * Real.log ((M : ℝ) - 1) := by linarith [h1]

/-- Selects a sparsity parameter `k` for the Fano lower bound on the `ℓ¹`-ball, ensuring the
separation and KL bounds are compatible with the regime hypothesis. -/
lemma fano_parameter_balancing {d : ℕ} (hd8 : 8 ≤ d)
    (σ R : ℝ) (_hσ : 0 < σ) (hR : 0 < R) (n : ℕ) (_hn : 0 < n)
    (ε : ℝ) (_hε : 0 < ε) (_hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
    (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)) :
    ∃ (k : ℕ), 1 ≤ k ∧ k ≤ d / 8 ∧
      (R ^ 2 / (2 * (k : ℝ)) ≥
        4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n))) ∧
      (128 * ↑n * R ^ 2 / σ ^ 2 ≤
        (k : ℝ) ^ 2 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ)))) := by
  refine ⟨1, le_refl 1, ?_, ?_, ?_⟩
  · omega
  · simp only [Nat.cast_one, mul_one]
    have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
    have hmin : min (R ^ 2) (R * σ * Real.log (↑d) / ↑n) ≤ R ^ 2 := min_le_left _ _
    calc R ^ 2 / 2 ≥ R ^ 2 / 512 := by
            apply div_le_div_of_nonneg_left (le_of_lt hR2) (by norm_num) (by norm_num)
          _ = 1 / 512 * R ^ 2 := by ring
          _ ≥ 1 / 512 * min (R ^ 2) (R * σ * Real.log (↑d) / ↑n) := by
              apply mul_le_mul_of_nonneg_left hmin (by norm_num)
          _ = 4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log (↑d) / ↑n)) := by ring
  · simp only [Nat.cast_one, one_pow, one_mul, mul_one]
    linarith

/-- Combines parameter balancing with the sparse Varshamov-Gilbert construction to obtain a
binary code witnessing the separation and KL bounds required for the `ℓ¹`-ball Fano lower bound. -/
lemma fano_kl_sparsity_bound {d : ℕ} (hd8 : 8 ≤ d)
    (σ R : ℝ) (hσ : 0 < σ) (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
    (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)) :

    ∃ (k : ℕ) (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)),
      1 ≤ k ∧ k ≤ d / 8 ∧ 5 ≤ M ∧
      (R ^ 2 / (2 * (k : ℝ)) ≥
        4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n))) ∧
      (↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) ≤ (1 / 8) * Real.log ((M : ℝ) - 1)) ∧
      Real.log (M : ℝ) ≥ (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ))) ∧
      (∀ j : Fin M, InfoTheory.l0norm_bool (ω j) = k) ∧
      (∀ j j' : Fin M, j ≠ j' → (InfoTheory.hammingDist (ω j) (ω j') : ℝ) ≥ (k : ℝ) / 2) := by

  obtain ⟨k, hk1, hkd, h_sep, h_k2_bound⟩ :=
    fano_parameter_balancing hd8 σ R hσ hR n hn ε hε hd_large h_regime


  obtain ⟨M, hM_pos, ω, hlogM, hM5, hweight, hhamming⟩ :=
    InfoTheory.sparse_varshamov_gilbert d k hk1 hkd

  refine ⟨k, M, hM_pos, ω, hk1, hkd, hM5, h_sep, ?_, hlogM, hweight, hhamming⟩
  exact kl_bound_from_k_squared hk1 hσ h_k2_bound hM5 hlogM

/-- Public form of `fano_kl_sparsity_bound`: selects the sparse code parameters
`(k, M, ω)` used to lower bound the `ℓ¹`-ball minimax risk. -/
theorem l1Ball_fano_sparsity_choice {d : ℕ} (hd8 : 8 ≤ d)
    (σ R : ℝ) (hσ : 0 < σ) (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
    (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)) :

    ∃ (k : ℕ) (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)),
      1 ≤ k ∧ k ≤ d / 8 ∧ 5 ≤ M ∧
      (R ^ 2 / (2 * (k : ℝ)) ≥
        4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n))) ∧
      (↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) ≤ (1 / 8) * Real.log ((M : ℝ) - 1)) ∧
      Real.log (M : ℝ) ≥ (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ))) ∧
      (∀ j : Fin M, InfoTheory.l0norm_bool (ω j) = k) ∧
      (∀ j j' : Fin M, j ≠ j' → (InfoTheory.hammingDist (ω j) (ω j') : ℝ) ≥ (k : ℝ) / 2) :=
  fano_kl_sparsity_bound hd8 σ R hσ hR n hn ε hε hd_large h_regime

/-- Builds an explicit codebook `θ : Fin M → ℝ^d` in the `ℓ¹`-ball satisfying the separation and
average-KL bounds needed by Fano's lemma. -/
theorem l1Ball_fano_parameter_existence {d : ℕ} (hd8 : 8 ≤ d)
    (σ R : ℝ) (hσ : 0 < σ) (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : Cor_5_13.IsGSM P σ n)
    (ε : ℝ) (hε : 0 < ε) (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
    (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)) :

    ∃ (M : ℕ) (θ : Fin M → Fin d → ℝ),
      2 ≤ M ∧ 5 ≤ M ∧
      (∀ j : Fin M, θ j ∈ l1Ball d R) ∧
      (∀ j k : Fin M, j ≠ k →
        InfoTheory.sqDist (θ j) (θ k) ≥
          4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n))) ∧
      (∃ κ : ℝ,
        κ ≤ (1 / 8) * Real.log ((M : ℝ) - 1) ∧
        (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M,
          (klDiv (P (θ j)) (P (θ k))).toReal ≤ κ) := by

  obtain ⟨k, M, hM_pos, ω, hk1, hkd, hM5, h_sep_bound, h_kl_bound, _hlogM, hweight, hhamming⟩ :=
    l1Ball_fano_sparsity_choice hd8 σ R hσ hR n hn ε hε hd_large h_regime


  let s := R / (k : ℝ)
  let θ : Fin M → Fin d → ℝ := fun j => Cor_5_13.scaledBoolVec (ω j) s
  refine ⟨M, θ, ?_, hM5, ?_, ?_, ?_⟩
  ·
    omega
  ·
    intro j
    exact scaledBoolVec_in_l1Ball (ω j) R k hR (by omega : 0 < k) (hweight j)
  ·
    intro j k' hjk

    have h_sqd : InfoTheory.sqDist (θ j) (θ k') =
        s ^ 2 * ↑(InfoTheory.hammingDist (ω j) (ω k')) :=
      Cor_5_13.sqDist_scaledBoolVec (ω j) (ω k') s
    rw [h_sqd]

    have h_ham := hhamming j k' hjk

    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega : 0 < k)
    have hs_eq : s = R / (k : ℝ) := rfl
    have hs_sq : s ^ 2 = R ^ 2 / (k : ℝ) ^ 2 := by
      rw [hs_eq, div_pow]

    calc s ^ 2 * ↑(InfoTheory.hammingDist (ω j) (ω k'))
        ≥ s ^ 2 * ((k : ℝ) / 2) := by
          apply mul_le_mul_of_nonneg_left h_ham (sq_nonneg s)
      _ = R ^ 2 / (k : ℝ) ^ 2 * ((k : ℝ) / 2) := by rw [hs_sq]
      _ = R ^ 2 / (2 * (k : ℝ)) := by field_simp
      _ ≥ 4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n)) := h_sep_bound
  ·

    refine ⟨↑n * R ^ 2 / ((k : ℝ) * σ ^ 2), ?_, ?_⟩
    ·
      exact h_kl_bound

    ·


      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega : 0 < k)
      haveI : ∀ θ', IsProbabilityMeasure (P θ') :=
        fun θ' => hP.isProbabilityMeasure hσ hn θ'

      have hKL_each : ∀ j k' : Fin M,
          (klDiv (P (θ j)) (P (θ k'))).toReal =
          ↑n * (s ^ 2 * ↑(InfoTheory.hammingDist (ω j) (ω k'))) / (2 * σ ^ 2) :=
        fun j k' => gsm_kl_scaledBoolVec P σ hσ n hn hP ω s j k'

      have h_ham_le : ∀ j k' : Fin M,
          (InfoTheory.hammingDist (ω j) (ω k') : ℝ) ≤ 2 * (k : ℝ) := by
        intro j k'
        have hw1 := hweight j
        have hw2 := hweight k'


        have h_card : InfoTheory.hammingDist (ω j) (ω k') ≤ 2 * k := by
          unfold InfoTheory.hammingDist InfoTheory.l0norm_bool at *
          calc (Finset.univ.filter fun i => (ω j) i ≠ (ω k') i).card
              ≤ ((Finset.univ.filter fun i => (ω j) i = true) ∪
                 (Finset.univ.filter fun i => (ω k') i = true)).card := by
                apply Finset.card_le_card
                intro i hi
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
                simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
                cases h1 : (ω j) i <;> cases h2 : (ω k') i <;> simp_all
            _ ≤ (Finset.univ.filter fun i => (ω j) i = true).card +
                 (Finset.univ.filter fun i => (ω k') i = true).card :=
                Finset.card_union_le _ _
            _ = k + k := by rw [hw1, hw2]
            _ = 2 * k := by ring
        exact_mod_cast h_card

      have hKL_le : ∀ j k' : Fin M,
          (klDiv (P (θ j)) (P (θ k'))).toReal ≤ ↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) := by
        intro j k'
        rw [hKL_each j k']
        have hs_sq : s ^ 2 = R ^ 2 / (k : ℝ) ^ 2 := by
          show (R / (k : ℝ)) ^ 2 = R ^ 2 / (k : ℝ) ^ 2
          rw [div_pow]
        rw [hs_sq]

        have h_ham := h_ham_le j k'
        have hσ2 : (0 : ℝ) < 2 * σ ^ 2 := by positivity


        calc ↑n * (R ^ 2 / (k : ℝ) ^ 2 * ↑(InfoTheory.hammingDist (ω j) (ω k'))) / (2 * σ ^ 2)
            ≤ ↑n * (R ^ 2 / (k : ℝ) ^ 2 * (2 * (k : ℝ))) / (2 * σ ^ 2) := by
              apply div_le_div_of_nonneg_right _ (by positivity : 0 < 2 * σ ^ 2).le
              apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg' n)
              apply mul_le_mul_of_nonneg_left h_ham
              exact div_nonneg (sq_nonneg R) (sq_nonneg (k : ℝ))
          _ = ↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) := by
              field_simp

      have h_sum : (∑ j : Fin M, ∑ k' : Fin M,
          (klDiv (P (θ j)) (P (θ k'))).toReal) ≤
          (M : ℝ) ^ 2 * (↑n * R ^ 2 / ((k : ℝ) * σ ^ 2)) := by
        calc ∑ j : Fin M, ∑ k' : Fin M,
              (klDiv (P (θ j)) (P (θ k'))).toReal
            ≤ ∑ j : Fin M, ∑ _ : Fin M,
                (↑n * R ^ 2 / ((k : ℝ) * σ ^ 2)) := by
              apply Finset.sum_le_sum
              intro j _
              apply Finset.sum_le_sum
              intro k' _
              exact hKL_le j k'
          _ = (M : ℝ) ^ 2 * (↑n * R ^ 2 / ((k : ℝ) * σ ^ 2)) := by
              simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
              ring

      have hM_pos_real : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
      have hM_sq_pos : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
      calc 1 / (M : ℝ) ^ 2 * ∑ j : Fin M, ∑ k' : Fin M,
              (klDiv (P (θ j)) (P (θ k'))).toReal
          ≤ 1 / (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 * (↑n * R ^ 2 / ((k : ℝ) * σ ^ 2))) := by
            apply mul_le_mul_of_nonneg_left h_sum
            positivity
        _ = ↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) := by
            field_simp

/-- Fano-based testing lower bound for the `ℓ¹`-ball: there exists `θ₀ ∈ B₁(R)` such that for
any measurable estimator the probability of large squared error is at least `1/4`. -/
theorem l1Ball_fano_testing_bound {d : ℕ} (hd8 : 8 ≤ d)
    (σ R : ℝ) (hσ : 0 < σ) (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : Cor_5_13.IsGSM P σ n)
    (ε : ℝ) (hε : 0 < ε) (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
    (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2))
    (θhat : (Fin d → ℝ) → (Fin d → ℝ))
    (hθhat_meas : Measurable θhat) :
    ∃ θ₀ ∈ l1Ball d R,
      (P θ₀ {Y | sqDist (θhat Y) θ₀ ≥
        1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n)}).toReal ≥ 1 / 4 := by

  obtain ⟨M, θ_code, hM2, hM5, h_in_ball, h_sep, κ, hκ_bound, hκ_kl⟩ :=
    l1Ball_fano_parameter_existence hd8 σ R hσ hR n hn P hP ε hε hd_large h_regime


  set ϕ := 1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n) with hϕ_def

  have hlog_pos : 0 < Real.log ↑d := by
    apply Real.log_pos
    have : (1 : ℝ) < ↑d := by exact_mod_cast (show 1 < d by omega)
    exact this
  have hϕ_pos : 0 < ϕ := by
    rw [hϕ_def]
    apply mul_pos (by norm_num : (0 : ℝ) < 1 / 2048)
    apply lt_min (by positivity)
    exact div_pos (mul_pos (mul_pos hR hσ) hlog_pos) (Nat.cast_pos.mpr hn)

  haveI : ∀ θ', IsProbabilityMeasure (P θ') :=
    fun θ' => hP.isProbabilityMeasure hσ hn θ'

  have hac : ∀ j k, P (θ_code j) ≪ P (θ_code k) :=
    fun j k => Cor_5_13.gsm_abs_continuous P σ hσ n hn hP (θ_code j) (θ_code k)

  have h_sep_sq : ∀ j k : Fin M, j ≠ k →
      InfoTheory.sqDist (θ_code j) (θ_code k) ≥ 4 * ϕ :=
    h_sep

  have hM3 : 3 ≤ M := le_trans (by norm_num : 3 ≤ 5) hM5
  have h_fano := InfoTheory.reduction_to_testing_fano hM3 P θ_code hac
    (fun j k => hP.hP_kl_ne_top (θ_code k) (θ_code j))
    ϕ hϕ_pos h_sep_sq κ hκ_kl θhat hθhat_meas

  have h_ge_quarter : (1 : ℝ) - (κ + Real.log 2) / Real.log ((M : ℝ) - 1) ≥ 1 / 4 :=
    l1Ball_fano_numerical_bound κ M hM5 hκ_bound

  have hM_pos : 0 < M := by omega
  haveI : Nonempty (Fin M) := ⟨⟨0, hM_pos⟩⟩
  have h_spec : ⨆ (j : Fin M),
      (P (θ_code j) {Y | InfoTheory.sqDist (θhat Y) (θ_code j) ≥ ϕ}).toReal ≥ 1 / 4 :=
    le_trans h_ge_quarter h_fano

  have h_bdd_above : BddAbove (Set.range fun j : Fin M =>
      (P (θ_code j) {Y | InfoTheory.sqDist (θhat Y) (θ_code j) ≥ ϕ}).toReal) := by
    refine ⟨1, ?_⟩
    rintro x ⟨j, rfl⟩
    exact ENNReal.toReal_le_of_le_ofReal one_pos.le
      (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  obtain ⟨j₀, _, hj₀_max⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin M => (P (θ_code j) {Y | InfoTheory.sqDist (θhat Y) (θ_code j) ≥ ϕ}).toReal)
    ⟨⟨0, hM_pos⟩, Finset.mem_univ _⟩
  have h_ciSup_le : ⨆ (j : Fin M),
      (P (θ_code j) {Y | InfoTheory.sqDist (θhat Y) (θ_code j) ≥ ϕ}).toReal ≤
      (P (θ_code j₀) {Y | InfoTheory.sqDist (θhat Y) (θ_code j₀) ≥ ϕ}).toReal := by
    apply ciSup_le
    intro j
    exact hj₀_max j (Finset.mem_univ _)
  have h_at_j₀ :
      (P (θ_code j₀) {Y | InfoTheory.sqDist (θhat Y) (θ_code j₀) ≥ ϕ}).toReal ≥ 1 / 4 := by
    linarith

  refine ⟨θ_code j₀, h_in_ball j₀, ?_⟩
  have h_eq : {Y | sqDist (θhat Y) (θ_code j₀) ≥ ϕ} =
      {Y | InfoTheory.sqDist (θhat Y) (θ_code j₀) ≥ ϕ} := by
    ext Y; simp [sqDist, InfoTheory.sqDist]
  rw [h_eq]
  exact h_at_j₀

/-- The supremum of risks over `θ ∈ B₁(R)` is bounded above in a GSM. -/
theorem gsm_bddAbove_risk_l1Ball {d : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (σ R : ℝ) (hσ : 0 < σ) (_hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (hP : Cor_5_13.IsGSM P σ n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)) :
    BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ l1Ball d R),
      ∫ Y, sqDist (θhat Y) θ ∂(P θ)) := by


  have hbdd_univ := Cor_5_13.gsm_bddAbove_risk P σ hσ n hn hP θhat
  obtain ⟨M, hM⟩ := hbdd_univ
  refine ⟨M, ?_⟩
  rintro x ⟨θ, rfl⟩

  show ⨆ (_ : θ ∈ l1Ball d R), ∫ Y, sqDist (θhat Y) θ ∂(P θ) ≤ M
  by_cases hθ : θ ∈ l1Ball d R
  ·
    haveI : Nonempty (θ ∈ l1Ball d R) := ⟨hθ⟩
    rw [ciSup_const]
    have hle : ∫ Y, sqDist (θhat Y) θ ∂(P θ) =
        ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ) := by
      congr 1
    rw [hle]
    have h_mem : (⨆ (_ : θ ∈ (Set.univ : Set (Fin d → ℝ))),
        ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ)) ∈
        Set.range (fun θ => ⨆ (_ : θ ∈ (Set.univ : Set (Fin d → ℝ))),
          ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ)) := Set.mem_range_self θ
    haveI : Nonempty (θ ∈ (Set.univ : Set (Fin d → ℝ))) := ⟨Set.mem_univ θ⟩
    calc ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ)
        = ⨆ (_ : θ ∈ (Set.univ : Set (Fin d → ℝ))),
            ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ) := (ciSup_const).symm
      _ ≤ M := hM h_mem
  ·
    have inst : IsEmpty (θ ∈ l1Ball d R) := isEmpty_Prop.mpr hθ
    rw [@Real.iSup_of_isEmpty _ inst]
    haveI : Nonempty (θ ∈ (Set.univ : Set (Fin d → ℝ))) := ⟨Set.mem_univ θ⟩
    have hM_ge : M ≥ ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ) := by
      calc ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ)
          = ⨆ (_ : θ ∈ (Set.univ : Set (Fin d → ℝ))),
              ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ) := (ciSup_const).symm
        _ ≤ M := hM (Set.mem_range_self θ)
    calc 0 ≤ ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ) :=
          integral_nonneg (fun Y => Finset.sum_nonneg (fun i _ => sq_nonneg _))
      _ ≤ M := hM_ge

/-- Fano-based minimax lower bound on `minimaxExpRisk_l1`: at least
`(1/8192) · min(R², R σ log d / n)` whenever the regime hypothesis holds. -/
theorem fano_minimax_lower_bound {d : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (σ R : ℝ) (n : ℕ) (hd8 : 8 ≤ d) (hσ : 0 < σ) (hR : 0 < R) (hn : 0 < n)
    (hP : Cor_5_13.IsGSM P σ n)
    (ε : ℝ) (hε : 0 < ε) (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
    (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)) :
    minimaxExpRisk_l1 P R ≥
      1 / 8192 * min (R ^ 2) (R * σ * Real.log d / n) := by

  set ϕ := 1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n) with hϕ_def

  have hlog_pos : 0 < Real.log ↑d := by
    apply Real.log_pos
    exact_mod_cast (show 1 < d by omega)
  have hϕ_pos : 0 < ϕ := by
    rw [hϕ_def]
    apply mul_pos (by norm_num : (0 : ℝ) < 1 / 2048)
    apply lt_min (by positivity)
    exact div_pos (mul_pos (mul_pos hR hσ) hlog_pos) (Nat.cast_pos.mpr hn)

  unfold minimaxExpRisk_l1
  rw [ge_iff_le]
  apply le_ciInf
  intro ⟨θhat, hθhat_meas⟩

  have h_test := l1Ball_fano_testing_bound hd8 σ R hσ hR n hn P hP ε hε hd_large h_regime
    θhat hθhat_meas
  obtain ⟨θ₀, hθ₀_mem, hθ₀_prob⟩ := h_test


  have h_bdd := gsm_bddAbove_risk_l1Ball P σ R hσ hR n hn hP θhat

  have h_sup_ge : ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (θhat Y) θ ∂P θ ≥
      ∫ Y, sqDist (θhat Y) θ₀ ∂P θ₀ := by
    apply le_ciSup_of_le h_bdd θ₀
    rw [ciSup_pos hθ₀_mem]


  have h_int_ge : ∫ Y, sqDist (θhat Y) θ₀ ∂P θ₀ ≥ 1 / 4 * ϕ := by
    have h_integ : Integrable (fun Y => sqDist (θhat Y) θ₀) (P θ₀) := by
      have h : (fun Y => sqDist (θhat Y) θ₀) = (fun Y => Cor_5_13.sqDist (θhat Y) θ₀) := by
        ext Y; simp [sqDist, Cor_5_13.sqDist]
      rw [h]
      exact Cor_5_13.gsm_integrable_sqDist P σ hσ n hn hP θhat θ₀
    have h_nonneg : 0 ≤ᵐ[P θ₀] (fun Y => sqDist (θhat Y) θ₀) :=
      Filter.Eventually.of_forall (fun Y => Finset.sum_nonneg (fun i _ => sq_nonneg _))

    have h_markov := mul_meas_ge_le_integral_of_nonneg h_nonneg h_integ ϕ

    rw [ge_iff_le]
    have h_markov' : ϕ * ((P θ₀) {Y | ϕ ≤ sqDist (θhat Y) θ₀}).toReal ≤
        ∫ Y, sqDist (θhat Y) θ₀ ∂P θ₀ := by
      rw [← Measure.real_def]
      exact h_markov
    calc 1 / 4 * ϕ = ϕ * (1 / 4) := by ring
      _ ≤ ϕ * ((P θ₀) {Y | ϕ ≤ sqDist (θhat Y) θ₀}).toReal := by
          gcongr
      _ ≤ ∫ Y, sqDist (θhat Y) θ₀ ∂P θ₀ := h_markov'


  calc 1 / 8192 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n)
      = 1 / 4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n)) := by ring
    _ = 1 / 4 * ϕ := by rw [hϕ_def]
    _ ≤ ∫ Y, sqDist (θhat Y) θ₀ ∂P θ₀ := h_int_ge
    _ ≤ ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (θhat Y) θ ∂P θ := h_sup_ge

/-- Restatement of `fano_minimax_lower_bound` with the inequality flipped. -/
theorem l1_ball_lower_bound {d : ℕ} (hd8 : 8 ≤ d) (σ R : ℝ) (hσ : 0 < σ)
    (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : Cor_5_13.IsGSM P σ n)
    (ε : ℝ) (hε : 0 < ε) (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
    (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)) :
    1 / 8192 * min (R ^ 2) (R * σ * Real.log d / n) ≤
      minimaxExpRisk_l1 P R :=
  fano_minimax_lower_bound P σ R n hd8 hσ hR hn hP ε hε hd_large h_regime

/-- Generic oracle inequality: if the constrained LS risk at `θ` is bounded by the loss to any
oracle `θ' ∈ B₁(R)` plus a width `W`, then it is bounded by the infimum over oracles plus `W`. -/
lemma gsm_oracle_inequality_with_width {d : ℕ} (_hd : 0 < d)
    (σ R : ℝ) (_hσ : 0 < σ) (_hR : 0 < R) (n : ℕ) (_hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (_hP : Cor_5_13.IsGSM P σ n)
    (θ : Fin d → ℝ) (hθ : θ ∈ l1Ball d R)
    (W : ℝ) (_hW : W ≥ 0)
    (hW_bound : ∀ θ' ∈ l1Ball d R,
      ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤
        sqDist θ' θ + W) :
    ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤
      (⨅ θ' ∈ l1Ball d R, sqDist θ' θ) + W := by
  have h_nonneg : ∀ θ' : Fin d → ℝ, 0 ≤ sqDist θ' θ :=
    fun θ' => Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h_bdd : BddBelow (⋃ i, Set.range fun (_ : i ∈ l1Ball d R) => sqDist i θ) := by
    use 0
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, ⟨_, rfl⟩⟩ := hx
    exact h_nonneg i


  have h_le_inf : ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) - W ≤
      ⨅ θ' ∈ l1Ball d R, sqDist θ' θ := by
    apply le_ciInf
    intro θ'
    by_cases hm : θ' ∈ l1Ball d R
    · haveI : Nonempty (θ' ∈ l1Ball d R) := ⟨hm⟩
      apply le_ciInf
      intro _
      linarith [hW_bound θ' hm]
    · show _ ≤ ⨅ (_ : θ' ∈ l1Ball d R), sqDist θ' θ
      simp only [iInf]
      have : (Set.range fun (_ : θ' ∈ l1Ball d R) => sqDist θ' θ) = ∅ := by
        ext x
        simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h, _⟩
        exact hm h
      rw [this, Real.sInf_empty]
      have h_self : sqDist θ θ = 0 := by simp [sqDist, sub_self]
      linarith [hW_bound θ hθ]
  linarith

/-- The constrained `ℓ¹`-ball LS estimator always returns a vector with `|θ̂(Y)|_1 ≤ R`. -/
lemma constrainedLS_l1norm_le {d : ℕ} (R : ℝ) (hR : 0 < R) (Y : Fin d → ℝ) :
    l1norm (constrainedLSEstimator d R Y) ≤ R := by
  unfold constrainedLSEstimator
  split
  next h =>
    exact h.choose_spec.1
  next _ =>

    show l1norm (fun _ => 0) ≤ R
    simp [l1norm, abs_of_nonneg]
    linarith

/-- The constrained `ℓ¹`-ball LS estimator achieves the minimum squared-distance to the data among
candidates in `B₁(R)`. -/
lemma constrainedLS_opt {d : ℕ} (R : ℝ) (Y : Fin d → ℝ)
    (u : Fin d → ℝ) (hu : u ∈ l1Ball d R) :
    sqDist Y (constrainedLSEstimator d R Y) ≤ sqDist Y u := by
  unfold constrainedLSEstimator
  split
  next h =>
    exact h.choose_spec.2 u hu
  next h =>


    exfalso
    apply h
    have hK : IsCompact (l1Ball d R) := by
      rw [Metric.isCompact_iff_isClosed_bounded]
      exact ⟨isClosed_le
          (continuous_finset_sum _ (fun i _ => (continuous_apply i).abs))
          continuous_const,
        Bornology.IsBounded.subset
          (Metric.isBounded_closedBall (x := (0 : Fin d → ℝ)) (r := max R 0))
          (fun θ hθ => by
            simp only [Metric.mem_closedBall, dist_zero_right]
            rw [pi_norm_le_iff_of_nonneg (le_max_right R 0)]
            intro i
            simp only [Real.norm_eq_abs]
            exact le_trans
              (Finset.single_le_sum (fun j _ => abs_nonneg (θ j)) (Finset.mem_univ i))
              (le_trans hθ (le_max_left R 0)))⟩
    have hne : (l1Ball d R).Nonempty := ⟨u, hu⟩
    have hcont : ContinuousOn (sqDist Y) (l1Ball d R) :=
      (continuous_finset_sum _ (fun i _ =>
        (continuous_const.sub (continuous_apply i)).pow 2)).continuousOn
    obtain ⟨x, hx_mem, hx_min⟩ := hK.exists_isMinOn hne hcont
    exact ⟨x, hx_mem, fun θ' hθ' => hx_min hθ'⟩

/-- Specializes the GSM cross-term bound to the constrained `ℓ¹`-ball LS estimator. -/
lemma constrainedLS_pointwise_bound_l1Ball {d : ℕ} (hd : 0 < d)
    (σ R : ℝ) (hσ : 0 < σ) (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : Cor_5_13.IsGSM P σ n)
    (θ : Fin d → ℝ) (_hθ : θ ∈ l1Ball d R)
    (θ' : Fin d → ℝ) (hθ' : θ' ∈ l1Ball d R) :
    ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤
      sqDist θ' θ + 2 * (σ ^ 2 / ↑n) * (R * Real.log ↑d / σ) := by
  exact hP.cross_term_bound hσ hn hd R hR θ θ'
    (constrainedLSEstimator d R) hθ'
    (fun Y => constrainedLS_l1norm_le R hR Y)
    (fun Y u hu => constrainedLS_opt R Y u hu)

/-- General oracle inequality at `θ ∈ B₁(R)`: the risk of `constrainedLSEstimator` is at most
the oracle infimum plus `2(σ²/n)(R log d / σ)`. -/
lemma oracle_inequality_constrainedLS_general {d : ℕ} (hd : 0 < d)
    (σ R : ℝ) (hσ : 0 < σ) (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : Cor_5_13.IsGSM P σ n)
    (θ : Fin d → ℝ) (hθ : θ ∈ l1Ball d R) :
    ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤
      (⨅ θ' ∈ l1Ball d R, sqDist θ' θ) +
        2 * (σ ^ 2 / ↑n) * (R * Real.log ↑d / σ) := by
  apply gsm_oracle_inequality_with_width hd σ R hσ hR n hn P hP θ hθ
  · positivity
  · exact fun θ' hθ' =>
      constrainedLS_pointwise_bound_l1Ball hd σ R hσ hR n hn P hP θ hθ θ' hθ'

/-- The infimum of `sqDist θ' θ` over `θ' ∈ B₁(R)` is zero whenever `θ ∈ B₁(R)`. -/
lemma infimum_sqDist_l1Ball_zero {d : ℕ} (R : ℝ)
    (θ : Fin d → ℝ) (hθ : θ ∈ l1Ball d R) :
    (⨅ θ' ∈ l1Ball d R, sqDist θ' θ) = 0 := by
  have h_self : sqDist θ θ = 0 := by simp [sqDist, sub_self]
  have h_nonneg : ∀ θ' : Fin d → ℝ, 0 ≤ sqDist θ' θ :=
    fun θ' => Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h_bdd : BddBelow (⋃ i, Set.range fun (_ : i ∈ l1Ball d R) => sqDist i θ) := by
    use 0
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, ⟨_, rfl⟩⟩ := hx
    exact h_nonneg i
  apply le_antisymm
  · calc ⨅ θ' ∈ l1Ball d R, sqDist θ' θ
        ≤ sqDist θ θ := ciInf₂_le h_bdd θ hθ
      _ = 0 := h_self
  · apply le_ciInf
    intro θ'
    by_cases hm : θ' ∈ l1Ball d R
    · haveI : Nonempty (θ' ∈ l1Ball d R) := ⟨hm⟩
      exact le_ciInf (fun _ => h_nonneg θ')
    ·

      show 0 ≤ ⨅ (_ : θ' ∈ l1Ball d R), sqDist θ' θ
      simp only [iInf]
      convert le_refl (0 : ℝ)
      convert Real.sInf_empty
      ext x
      simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h, rfl⟩
      exact hm h

/-- Pointwise risk bound for the constrained `ℓ¹`-ball LS estimator at `θ ∈ B₁(R)`:
`E[‖θ̂ - θ‖²] ≤ 2 R σ log d / n`. -/
theorem gsm_constrainedLS_oracle_inequality_l1Ball {d : ℕ} (hd : 0 < d)
    (σ R : ℝ) (hσ : 0 < σ) (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : Cor_5_13.IsGSM P σ n)
    (θ : Fin d → ℝ) (hθ : θ ∈ l1Ball d R) :
    ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤
      2 * (R * σ * Real.log ↑d / ↑n) := by

  have h_oracle := oracle_inequality_constrainedLS_general hd σ R hσ hR n hn P hP θ hθ

  have h_inf_zero := infimum_sqDist_l1Ball_zero R θ hθ
  rw [h_inf_zero] at h_oracle

  have h_eq : 0 + 2 * (σ ^ 2 / ↑n) * (R * Real.log ↑d / σ) =
      2 * (R * σ * Real.log ↑d / ↑n) := by
    field_simp
    ring
  linarith

/-- Pointwise risk bound for the constrained LS estimator on `B₁(R)`, including the high-dimensional
hypothesis `d ≥ n^(1/2+ε)` for compatibility with downstream uses. -/
theorem constrainedLS_risk_pointwise {d : ℕ} (hd : 0 < d)
    (σ R : ℝ) (hσ : 0 < σ) (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : Cor_5_13.IsGSM P σ n)
    (_ε : ℝ) (_hε : 0 < _ε) (_hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + _ε))
    (θ : Fin d → ℝ) (hθ : θ ∈ l1Ball d R) :
    ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤
      2 * (R * σ * Real.log ↑d / ↑n) :=
  gsm_constrainedLS_oracle_inequality_l1Ball hd σ R hσ hR n hn P hP θ hθ

/-- Sup-risk version of the oracle inequality: the worst-case risk of the constrained LS estimator
over `B₁(R)` is at most `2 R σ log d / n`. -/
theorem oracle_inequality_constrainedLS {d : ℕ} (hd : 0 < d)
    (σ R : ℝ) (hσ : 0 < σ) (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : Cor_5_13.IsGSM P σ n)
    (ε : ℝ) (hε : 0 < ε) (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε)) :
    ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤
      2 * (R * σ * Real.log ↑d / ↑n) := by
  apply ciSup_le
  intro θ
  by_cases hθ : θ ∈ l1Ball d R
  · simp only [hθ, ciSup_pos]
    exact constrainedLS_risk_pointwise hd σ R hσ hR n hn P hP ε hε hd_large θ hθ
  · simp only [hθ, ciSup_neg, not_false_eq_true]
    rw [Real.sSup_empty]
    positivity

/-- In the large-radius regime `R ≥ σ log d / n`, the constrained LS estimator attains worst-case
risk at most `2 · min(R², R σ log d / n)`. -/
theorem constrainedLS_attains {d : ℕ} (hd : 0 < d) (σ R : ℝ) (hσ : 0 < σ)
    (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : Cor_5_13.IsGSM P σ n)
    (ε : ℝ) (hε : 0 < ε) (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
    (hR_large : R ≥ σ * Real.log ↑d / ↑n) :
    ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤
      2 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n) := by


  have h_min_eq : min (R ^ 2) (R * σ * Real.log ↑d / ↑n) =
      R * σ * Real.log ↑d / ↑n := by
    apply min_eq_right
    calc R * σ * Real.log ↑d / ↑n
        = R * (σ * Real.log ↑d / ↑n) := by ring
      _ ≤ R * R := by
          apply mul_le_mul_of_nonneg_left hR_large (le_of_lt hR)
      _ = R ^ 2 := by ring
  rw [h_min_eq]
  exact oracle_inequality_constrainedLS hd σ R hσ hR n hn P hP ε hε hd_large

/-- Minimax upper bound for `B₁(R)`: combines the constrained LS and trivial estimators to obtain
`minimaxExpRisk_l1 P R ≤ 2 · min(R², R σ log d / n)`. -/
theorem l1_ball_upper_bound {d : ℕ} (hd : 0 < d) (σ R : ℝ) (hσ : 0 < σ)
    (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : Cor_5_13.IsGSM P σ n)
    (ε : ℝ) (hε : 0 < ε) (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε)) :
    minimaxExpRisk_l1 P R ≤
      2 * min (R ^ 2) (R * σ * Real.log d / n) := by


  unfold minimaxExpRisk_l1

  have h_bdd : BddBelow (Set.range fun (θhat : MeasEstimator d) =>
      ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (θhat.1 Y) θ ∂(P θ)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨θhat, rfl⟩
    apply Real.iSup_nonneg
    intro θ
    apply Real.iSup_nonneg
    intro _
    exact integral_nonneg (fun Y => Finset.sum_nonneg (fun i _ => sq_nonneg _))

  by_cases hR_case : R ≥ σ * Real.log ↑d / ↑n
  ·
    exact ciInf_le_of_le h_bdd (constrainedLSMeasEstimator d R)
      (constrainedLS_attains hd σ R hσ hR n hn P hP ε hε hd_large hR_case)
  ·
    simp only [not_le] at hR_case
    exact ciInf_le_of_le h_bdd (trivialMeasEstimator d)
      (trivialEstimator_attains σ R hσ hR n hn P hP hR_case)

/-- The `ℓ¹`-ball is monotone in its radius. -/
lemma l1Ball_mono {d : ℕ} {R R' : ℝ} (h : R' ≤ R) : l1Ball d R' ⊆ l1Ball d R :=
  fun _ hθ => le_trans hθ h

/-- Monotonicity of the `ℓ¹`-ball minimax expected risk in the radius `R`. -/
lemma minimaxExpRisk_l1_mono {d : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (hP : Cor_5_13.IsGSM P σ n)
    {R R' : ℝ} (hR : 0 < R) (_hR' : 0 < R') (hRR' : R' ≤ R) :
    minimaxExpRisk_l1 P R' ≤ minimaxExpRisk_l1 P R := by
  unfold minimaxExpRisk_l1
  apply ciInf_mono
  ·
    refine ⟨0, ?_⟩
    rintro x ⟨θhat, rfl⟩
    apply Real.iSup_nonneg
    intro θ
    apply Real.iSup_nonneg
    intro _
    exact integral_nonneg (fun Y => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  · intro θhat

    have h_bdd_R := gsm_bddAbove_risk_l1Ball P σ R hσ hR n hn hP θhat.1

    apply ciSup_le
    intro θ
    by_cases hθ : θ ∈ l1Ball d R'
    · simp only [hθ, ciSup_pos]
      have hθR := l1Ball_mono hRR' hθ

      exact le_ciSup_of_le h_bdd_R θ (by
        haveI : Nonempty (θ ∈ l1Ball d R) := ⟨hθR⟩
        rw [ciSup_pos hθR])
    · simp only [hθ, ciSup_neg, not_false_eq_true]
      rw [Real.sSup_empty]
      apply Real.iSup_nonneg
      intro θ'
      apply Real.iSup_nonneg
      intro _
      exact integral_nonneg (fun Y => Finset.sum_nonneg (fun i _ => sq_nonneg _))

/-- **Corollary 5.16** (`ℓ¹`-ball minimax rate): for the `ℓ¹`-ball `B₁(R) ⊂ ℝ^d` in the
high-dimensional regime `d ≥ n^(1/2+ε)`, the minimax rate of estimation in the Gaussian sequence
model is `φ(B₁(R)) = min(R², R σ log d / n)` (up to constants), attained by the constrained
least squares estimator when `R ≥ σ log d / n` and by the trivial estimator `θ̂ = 0` otherwise. -/
theorem cor_5_16 {d : ℕ} (hd8 : 8 ≤ d) (σ R : ℝ) (hσ : 0 < σ) (hR : 0 < R)
    (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : Cor_5_13.IsGSM P σ n)
    (ε : ℝ) (hε : 0 < ε) (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε)) :
    ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧
    c * min (R ^ 2) (R * σ * Real.log d / n) ≤
      minimaxExpRisk_l1 P R ∧
    minimaxExpRisk_l1 P R ≤
      C * min (R ^ 2) (R * σ * Real.log d / n) ∧

    (R ≥ σ * Real.log d / n →
      ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤
        C * min (R ^ 2) (R * σ * Real.log d / n)) ∧
    (R < σ * Real.log d / n →
      ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (trivialEstimator d Y) θ ∂(P θ) ≤
        C * min (R ^ 2) (R * σ * Real.log d / n)) := by
  have hd : 0 < d := by omega
  have hlog_pos : 0 < Real.log ↑d := by
    have : (1 : ℝ) < ↑d := by exact_mod_cast (show 1 < d by omega)
    exact Real.log_pos this
  have hmin_pos : 0 < min (R ^ 2) (R * σ * Real.log ↑d / ↑n) :=
    lt_min (by positivity) (div_pos (mul_pos (mul_pos hR hσ) hlog_pos) (Nat.cast_pos.mpr hn))

  have h_upper := l1_ball_upper_bound hd σ R hσ hR n hn P hP ε hε hd_large

  by_cases h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)
  ·
    exact ⟨1 / 8192, 2, by norm_num, by norm_num,
      l1_ball_lower_bound hd8 σ R hσ hR n hn P hP ε hε hd_large h_regime,
      h_upper,
      fun hR_large => constrainedLS_attains hd σ R hσ hR n hn P hP ε hε hd_large hR_large,
      fun hR_small => trivialEstimator_attains σ R hσ hR n hn P hP hR_small⟩
  ·

    simp only [not_le] at h_regime
    set R₀ := σ * Real.sqrt (Real.log (1 + ↑d / 2) / (128 * ↑n)) with hR₀_def

    have hR₀_pos : 0 < R₀ := by
      apply mul_pos hσ (Real.sqrt_pos_of_pos _)
      apply div_pos
      · apply Real.log_pos
        have : (2 : ℝ) ≤ ↑d := by exact_mod_cast (show 2 ≤ d by omega)
        linarith
      · positivity

    have hR₀_lt_R : R₀ < R := by
      have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
      have hL_pos : 0 < Real.log (1 + ↑d / 2) := by
        apply Real.log_pos
        have : (2 : ℝ) ≤ ↑d := by exact_mod_cast (show 2 ≤ d by omega)
        linarith
      suffices h : σ ^ 2 * (Real.log (1 + ↑d / 2) / (128 * ↑n)) < R ^ 2 by
        rw [hR₀_def, ← Real.sqrt_sq hσ.le, ← Real.sqrt_mul (sq_nonneg σ),
            ← Real.sqrt_sq hR.le]
        exact Real.sqrt_lt_sqrt (by positivity) h
      have h1 := h_regime
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < σ ^ 2)] at h1
      rw [show σ ^ 2 * (Real.log (1 + ↑d / 2) / (128 * ↑n)) =
        Real.log (1 + ↑d / 2) * σ ^ 2 / (128 * ↑n) from by ring]
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < 128 * ↑n)]
      linarith

    have hR₀_fano : 128 * ↑n * R₀ ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2) := by
      rw [hR₀_def, mul_pow, Real.sq_sqrt (div_nonneg
        (Real.log_nonneg (by linarith [show (2:ℝ) ≤ ↑d from by exact_mod_cast (show 2 ≤ d by omega)]))
        (by positivity))]
      have h_eq : 128 * ↑n * (σ ^ 2 * (Real.log (1 + ↑d / 2) / (128 * ↑n))) / σ ^ 2 =
        Real.log (1 + ↑d / 2) := by
        field_simp
      linarith

    have h_fano_R₀ : minimaxExpRisk_l1 P R₀ ≥
        1 / 8192 * min (R₀ ^ 2) (R₀ * σ * Real.log ↑d / ↑n) :=
      fano_minimax_lower_bound P σ R₀ n hd8 hσ hR₀_pos hn hP ε hε hd_large hR₀_fano

    have h_mono : minimaxExpRisk_l1 P R₀ ≤ minimaxExpRisk_l1 P R :=
      minimaxExpRisk_l1_mono P σ hσ n hn hP hR hR₀_pos hR₀_lt_R.le

    have h_lb_R₀ : 1 / 8192 * min (R₀ ^ 2) (R₀ * σ * Real.log ↑d / ↑n) ≤
        minimaxExpRisk_l1 P R := le_trans h_fano_R₀ h_mono

    have hmin_R₀_pos : 0 < min (R₀ ^ 2) (R₀ * σ * Real.log ↑d / ↑n) :=
      lt_min (by positivity) (div_pos (mul_pos (mul_pos hR₀_pos hσ) hlog_pos)
        (Nat.cast_pos.mpr hn))


    set c := 1 / 8192 * min (R₀ ^ 2) (R₀ * σ * Real.log ↑d / ↑n) / R ^ 2 with hc_def
    have hc_pos : 0 < c := by positivity
    have h_lower : c * min (R ^ 2) (R * σ * Real.log ↑d / ↑n) ≤
        minimaxExpRisk_l1 P R := by
      calc c * min (R ^ 2) (R * σ * Real.log ↑d / ↑n)
          ≤ c * R ^ 2 := by gcongr; exact min_le_left _ _
        _ = 1 / 8192 * min (R₀ ^ 2) (R₀ * σ * Real.log ↑d / ↑n) := by
            rw [hc_def]; field_simp
        _ ≤ minimaxExpRisk_l1 P R := h_lb_R₀
    exact ⟨c, 2, hc_pos, by norm_num,
      h_lower,
      h_upper,
      fun hR_large => constrainedLS_attains hd σ R hσ hR n hn P hP ε hε hd_large hR_large,
      fun hR_small => trivialEstimator_attains σ R hσ hR n hn P hP hR_small⟩

end MinimaxL1Ball

end
