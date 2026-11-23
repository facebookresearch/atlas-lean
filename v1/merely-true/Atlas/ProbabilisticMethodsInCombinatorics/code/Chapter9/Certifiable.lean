/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.WeightedCertificates
import Atlas.ProbabilisticMethodsInCombinatorics.code.Certifiable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option maxHeartbeats 800000

open MeasureTheory Real Finset Set

noncomputable section

namespace TalagrandCertifiable

variable {n : ℕ} {Ω : Fin n → Type*}

/-- A function $f$ is Hamming-Lipschitz if $|f(x) - f(y)|$ is at most the Hamming distance
between $x$ and $y$ (the number of coordinates where they differ). -/
def IsHammingLipschitz [∀ i, DecidableEq (Ω i)]
    (f : ((i : Fin n) → Ω i) → ℝ) : Prop :=
  ∀ x y : (i : Fin n) → Ω i,
    |f x - f y| ≤ (Finset.univ.filter fun i => x i ≠ y i).card

/-- The upper level set $\{x : f(x) \geq r\}$ is $s$-certifiable (Definition 9.5.20). -/
def UpperLevelCertifiable [∀ i, DecidableEq (Ω i)]
    (f : ((i : Fin n) → Ω i) → ℝ) (r : ℝ) (s : ℕ) : Prop :=
  Certifiable.IsCertifiable (Ω := Ω) s {x | f x ≥ r}



/-- $m$ is a median of $f$ under the product measure $\prod_i \mu_i$:
both $\{f \leq m\}$ and $\{f \geq m\}$ have probability at least $1/2$. -/
def IsMedianPi
    {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i))
    (f : ((i : Fin n) → Ω i) → ℝ)
    (m : ℝ) : Prop :=
  (1 : ℝ) / 2 ≤ (Measure.pi μ {x | f x ≤ m}).toReal ∧
  (1 : ℝ) / 2 ≤ (Measure.pi μ {x | f x ≥ m}).toReal


/-- Technical lemma: for any $K > 0$ and $\varepsilon > 0$, one can choose $C$ large enough
that $2\exp(-C^2/(4K)) + 2\exp(-C^2/(4(K+C))) \leq \varepsilon$. -/
lemma tail_sum_small (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      2 * Real.exp (-(C ^ 2) / (4 * K)) +
      2 * Real.exp (-(C ^ 2) / (4 * (K + C))) ≤ ε := by
  set C := max (2 * K + 1) (8 * Real.log (4 / ε) + 1) with hC_def
  use C
  refine ⟨lt_of_lt_of_le (by linarith : (0:ℝ) < 2 * K + 1) (le_max_left _ _), ?_⟩
  have hC_ge_2K : 2 * K < C := lt_of_lt_of_le (by linarith : 2*K < 2*K+1) (le_max_left _ _)
  have hC_pos : (0 : ℝ) < C := by linarith
  have hKC_le : K + C ≤ 2 * C := by linarith
  have h_exp_lower : C ^ 2 / (4 * (K + C)) ≥ C / 8 := by
    rw [ge_iff_le, div_le_div_iff₀ (by positivity : (0:ℝ) < 8)
      (by positivity : (0:ℝ) < 4 * (K+C))]
    nlinarith [sq_nonneg C]
  have hexp1 : Real.exp (-(C ^ 2) / (4 * K)) ≤ Real.exp (-C / 8) := by
    apply Real.exp_le_exp.mpr
    have h_CK : C ^ 2 / (4 * K) ≥ C / 8 := le_trans h_exp_lower.le
      (div_le_div_of_nonneg_left (by positivity : 0 ≤ C ^ 2)
        (by positivity : 0 < 4 * K) (by linarith))
    linarith [neg_le_neg h_CK.le,
      show -(C ^ 2) / (4 * K) = -(C ^ 2 / (4 * K)) from by ring,
      show -C / 8 = -(C / 8) from by ring]
  have hexp2 : Real.exp (-(C ^ 2) / (4 * (K + C))) ≤ Real.exp (-C / 8) := by
    apply Real.exp_le_exp.mpr
    linarith [neg_le_neg h_exp_lower.le,
      show -(C ^ 2) / (4 * (K + C)) = -(C ^ 2 / (4 * (K + C))) from by ring,
      show -C / 8 = -(C / 8) from by ring]
  have htotal : 2 * Real.exp (-(C ^ 2) / (4 * K)) +
      2 * Real.exp (-(C ^ 2) / (4 * (K + C))) ≤ 4 * Real.exp (-C / 8) := by
    nlinarith [Real.exp_pos (-(C ^ 2) / (4 * K)), Real.exp_pos (-C / 8)]
  suffices h : 4 * Real.exp (-C / 8) ≤ ε from le_trans htotal h
  have hC_ge_log : C ≥ 8 * Real.log (4 / ε) := by
    linarith [le_max_right (2 * K + 1) (8 * Real.log (4 / ε) + 1)]
  have hexp_bound : Real.exp (-C / 8) ≤ ε / 4 := by
    calc Real.exp (-C / 8)
        = Real.exp (-(C / 8)) := by ring_nf
      _ ≤ Real.exp (-(Real.log (4 / ε))) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = (4 / ε)⁻¹ := by
          rw [Real.exp_neg, Real.exp_log (by positivity : (0:ℝ) < 4 / ε)]
      _ = ε / 4 := by field_simp
  linarith [Real.exp_pos (-C / 8)]

/-- Concentration of the longest-increasing-subsequence-type statistic: if the median $m$ of
$f$ satisfies $m \leq K\sqrt{n}$ and the Talagrand tail bounds hold, then for every
$\varepsilon > 0$ there exists $C$ such that $\mathbb{P}(|f - m| > C n^{1/4}) \leq \varepsilon$. -/
theorem lis_concentration
    {n : ℕ} (hn : 1 ≤ n)
    {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : ((i : Fin n) → Ω i) → ℝ)
    (m : ℝ) (hm_pos : 1 ≤ m)

    (K : ℝ) (hK : 0 < K) (hm_bound : m ≤ K * Real.sqrt n)

    (h_lower : ∀ t : ℝ, 0 ≤ t →
      (Measure.pi μ {x | f x ≤ m - t}).toReal ≤
        2 * Real.exp (-(t ^ 2) / (4 * m)))

    (h_upper : ∀ t : ℝ, 0 ≤ t →
      (Measure.pi μ {x | f x ≥ m + t}).toReal ≤
        2 * Real.exp (-(t ^ 2) / (4 * (m + t))))

    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      (Measure.pi μ {x | |f x - m| > C * (n : ℝ) ^ ((1:ℝ)/4)}).toReal ≤ ε := by
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ := tail_sum_small K hK ε hε
  use C₀
  refine ⟨hC₀_pos, ?_⟩
  set t := C₀ * (n : ℝ) ^ ((1:ℝ)/4)
  have ht_pos : (0 : ℝ) ≤ t := by positivity

  have h_subset : {x | |f x - m| > t} ⊆
      {x | f x ≤ m - t} ∪ {x | f x ≥ m + t} := by
    intro x hx
    simp only [Set.mem_setOf_eq, gt_iff_lt] at hx
    have habs := hx
    rw [lt_abs] at habs
    cases habs with
    | inl h =>
      right
      show f x ≥ m + t
      linarith
    | inr h =>
      left
      show f x ≤ m - t
      linarith

  have h_meas_le : (Measure.pi μ {x | |f x - m| > t}).toReal ≤
      (Measure.pi μ {x | f x ≤ m - t}).toReal +
        (Measure.pi μ {x | f x ≥ m + t}).toReal := by
    calc (Measure.pi μ {x | |f x - m| > t}).toReal
        ≤ (Measure.pi μ ({x | f x ≤ m - t} ∪ {x | f x ≥ m + t})).toReal := by
          apply ENNReal.toReal_mono (measure_ne_top _ _)
          exact measure_mono h_subset
      _ ≤ (Measure.pi μ {x | f x ≤ m - t} +
            Measure.pi μ {x | f x ≥ m + t}).toReal := by
          apply ENNReal.toReal_mono
          · exact ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
          · exact measure_union_le _ _
      _ = (Measure.pi μ {x | f x ≤ m - t}).toReal +
            (Measure.pi μ {x | f x ≥ m + t}).toReal :=
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)

  have h_low := h_lower t ht_pos
  have h_up := h_upper t ht_pos

  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsqrt_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have h_t_sq : t ^ 2 = C₀ ^ 2 * Real.sqrt n := by
    show (C₀ * (n : ℝ) ^ ((1:ℝ)/4)) ^ 2 = C₀ ^ 2 * Real.sqrt n
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((n : ℝ) ^ ((1:ℝ)/4)) 2,
        ← Real.rpow_mul (le_of_lt hn_pos)]
    norm_num
    rw [← Real.sqrt_eq_rpow]

  have h_exp_lower : Real.exp (-(t ^ 2) / (4 * m)) ≤
      Real.exp (-(C₀ ^ 2) / (4 * K)) := by
    apply Real.exp_le_exp.mpr
    rw [h_t_sq]
    have h1 : C₀ ^ 2 * Real.sqrt n / (4 * m) ≥ C₀ ^ 2 / (4 * K) := by
      rw [ge_iff_le, div_le_div_iff₀ (by positivity : (0:ℝ) < 4 * K)
        (by positivity : (0:ℝ) < 4 * m)]
      nlinarith [sq_nonneg C₀]
    linarith [neg_le_neg h1.le,
      show -(C₀ ^ 2 * Real.sqrt n) / (4 * m) =
        -(C₀ ^ 2 * Real.sqrt n / (4 * m)) from by ring,
      show -(C₀ ^ 2) / (4 * K) = -(C₀ ^ 2 / (4 * K)) from by ring]


  have h_n14_le_sqrt : (n : ℝ) ^ ((1:ℝ)/4) ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn) (by norm_num)
  have h_mt_bound : m + t ≤ (K + C₀) * Real.sqrt n := by
    calc m + t = m + C₀ * (n : ℝ) ^ ((1:ℝ)/4) := rfl
      _ ≤ K * Real.sqrt n + C₀ * Real.sqrt n := by
          linarith [mul_le_mul_of_nonneg_left h_n14_le_sqrt (le_of_lt hC₀_pos)]
      _ = (K + C₀) * Real.sqrt n := by ring
  have h_exp_upper : Real.exp (-(t ^ 2) / (4 * (m + t))) ≤
      Real.exp (-(C₀ ^ 2) / (4 * (K + C₀))) := by
    apply Real.exp_le_exp.mpr
    rw [h_t_sq]
    have hmt_pos : (0 : ℝ) < m + t := by linarith [ht_pos]
    have h1 : C₀ ^ 2 * Real.sqrt n / (4 * (m + t)) ≥
        C₀ ^ 2 / (4 * (K + C₀)) := by
      rw [ge_iff_le, div_le_div_iff₀ (by positivity : (0:ℝ) < 4 * (K + C₀))
        (by positivity : (0:ℝ) < 4 * (m + t))]
      nlinarith [sq_nonneg C₀]
    linarith [neg_le_neg h1.le,
      show -(C₀ ^ 2 * Real.sqrt n) / (4 * (m + t)) =
        -(C₀ ^ 2 * Real.sqrt n / (4 * (m + t))) from by ring,
      show -(C₀ ^ 2) / (4 * (K + C₀)) =
        -(C₀ ^ 2 / (4 * (K + C₀))) from by ring]

  calc (Measure.pi μ {x | |f x - m| > t}).toReal
      ≤ (Measure.pi μ {x | f x ≤ m - t}).toReal +
          (Measure.pi μ {x | f x ≥ m + t}).toReal := h_meas_le
    _ ≤ 2 * Real.exp (-(t ^ 2) / (4 * m)) +
          2 * Real.exp (-(t ^ 2) / (4 * (m + t))) := by linarith
    _ ≤ 2 * Real.exp (-(C₀ ^ 2) / (4 * K)) +
          2 * Real.exp (-(C₀ ^ 2) / (4 * (K + C₀))) := by
        nlinarith [Real.exp_pos (-(t ^ 2) / (4 * m)),
          Real.exp_pos (-(t ^ 2) / (4 * (m + t)))]
    _ ≤ ε := hC₀_bound

end TalagrandCertifiable
