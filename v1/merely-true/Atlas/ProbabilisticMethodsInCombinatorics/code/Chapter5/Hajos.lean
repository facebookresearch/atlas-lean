/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Nat.Choose.Bounds

open Filter Topology Real Asymptotics SimpleGraph

set_option maxHeartbeats 400000

namespace Hajos

/-- The threshold $t = \lceil 10 \sqrt{n} \rceil$ used in Theorem 5.3.2: we show that
$G(n, 1/2)$ has no $K_t$-subdivision with high probability. -/
noncomputable def hajosParam (n : ℕ) : ℕ := ⌈10 * Real.sqrt (n : ℝ)⌉₊

/-- The union bound on the probability that $G(n, 1/2)$ contains a $K_t$-subdivision,
for $t = \lceil 10\sqrt n \rceil$: $\binom{n}{t} \cdot e^{-t^2/10}$. -/
noncomputable def subdivisionUnionBound (n : ℕ) : ℝ :=
  (n.choose (hajosParam n) : ℝ) * Real.exp (-(hajosParam n : ℝ) ^ 2 / 10)

/-- Lower bound on `hajosParam`: $10\sqrt n \leq \lceil 10\sqrt n \rceil$. -/
lemma hajosParam_ge (n : ℕ) : 10 * Real.sqrt (n : ℝ) ≤ (hajosParam n : ℝ) :=
  Nat.le_ceil _

/-- Upper bound on `hajosParam`: $\lceil 10\sqrt n \rceil \leq 10\sqrt n + 1$. -/
lemma hajosParam_le (n : ℕ) : (hajosParam n : ℝ) ≤ 10 * Real.sqrt (n : ℝ) + 1 :=
  (Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).le

/-- Squaring the lower bound on `hajosParam`: $100 n \leq t^2$. -/
lemma hajosParam_sq_ge (n : ℕ) : 100 * (n : ℝ) ≤ ((hajosParam n : ℕ) : ℝ) ^ 2 := by
  have h := hajosParam_ge n
  have ht_nn : (0 : ℝ) ≤ ((hajosParam n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h10_nn : (0:ℝ) ≤ 10 * Real.sqrt (n : ℝ) := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc (100 : ℝ) * (n : ℝ) = (10 * Real.sqrt (n : ℝ)) ^ 2 := by
        rw [mul_pow, sq_sqrt (Nat.cast_nonneg n)]; ring
    _ ≤ ((hajosParam n : ℕ) : ℝ) ^ 2 := sq_le_sq' (by linarith) h

/-- The union bound `subdivisionUnionBound` is nonnegative. -/
lemma subdivisionUnionBound_nonneg (n : ℕ) : 0 ≤ subdivisionUnionBound n := by
  unfold subdivisionUnionBound
  exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)

/-- For all sufficiently large $n$, $\log n \leq \tfrac{1}{10} \sqrt n$. -/
lemma log_le_sqrt_div_ten :
    ∀ᶠ (n : ℕ) in atTop, Real.log (n : ℝ) ≤ (1/10) * Real.sqrt (n : ℝ) := by
  have h := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)).bound
    (show (0:ℝ) < 1/10 by norm_num)
  rw [Filter.eventually_atTop] at h ⊢
  obtain ⟨N, hN⟩ := h
  refine ⟨max (Nat.ceil N) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnN : N ≤ (n : ℝ) := by
    calc N ≤ ↑(Nat.ceil N) := Nat.le_ceil N
    _ ≤ ↑(max (Nat.ceil N) 1) := by exact_mod_cast le_max_left _ _
    _ ≤ ↑n := by exact_mod_cast hn
  have h1 := hN (n : ℝ) hnN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ n) _)] at h1
  rw [Real.norm_of_nonneg (Real.log_nonneg hnR)] at h1
  rw [Real.sqrt_eq_rpow]; linarith

/-- Asymptotic comparison: for all sufficiently large $n$, $t \log n \leq 2n$ where
$t = \lceil 10\sqrt n \rceil$. -/
lemma hajosParam_log_bound :
    ∀ᶠ (n : ℕ) in atTop,
      (hajosParam n : ℝ) * Real.log (n : ℝ) ≤ 2 * (n : ℝ) := by
  filter_upwards [log_le_sqrt_div_ten, Filter.eventually_ge_atTop 1] with n hlog hn1
  have ht_le := hajosParam_le n
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrt_le_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    have := Real.sqrt_le_sqrt (show (n:ℝ) ≤ (n:ℝ)^2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ n)] at this
  have step1 : (hajosParam n : ℝ) * Real.log (n : ℝ)
      ≤ (10 * Real.sqrt (n : ℝ) + 1) * ((1/10) * Real.sqrt (n : ℝ)) := by
    gcongr
  have step2 : (10 * Real.sqrt (n : ℝ) + 1) * ((1/10) * Real.sqrt (n : ℝ))
      = Real.sqrt (n : ℝ) ^ 2 + (1/10) * Real.sqrt (n : ℝ) := by ring
  have step3 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := sq_sqrt (Nat.cast_nonneg n)
  linarith

/-- Rewrite a natural power as $n^t = \exp(t \log n)$ when $n > 0$. -/
lemma pow_eq_exp_mul_log (n : ℕ) (hn : 0 < (n : ℝ)) (t : ℕ) :
    (n : ℝ) ^ t = Real.exp ((t : ℝ) * Real.log (n : ℝ)) := by
  rw [← Real.rpow_natCast (n : ℝ) t, Real.rpow_def_of_pos hn]
  ring_nf

/-- The sequence $e^{-n}$ tends to $0$ as $n \to \infty$. -/
lemma tendsto_exp_neg_nat :
    Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (nhds 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)

/-- For all sufficiently large $n$, $\binom{n}{t} e^{-t^2/10} \leq e^{-n}$ with
$t = \lceil 10\sqrt n \rceil$. -/
lemma subdivisionUnionBound_le_exp :
    ∀ᶠ (n : ℕ) in atTop,
      subdivisionUnionBound n ≤ Real.exp (-(n : ℝ)) := by
  filter_upwards [hajosParam_log_bound, Filter.eventually_ge_atTop 1] with n hlog hn1
  unfold subdivisionUnionBound
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  calc (n.choose (hajosParam n) : ℝ) * Real.exp (-(hajosParam n : ℝ) ^ 2 / 10)
      ≤ (n : ℝ) ^ (hajosParam n) * Real.exp (-(hajosParam n : ℝ) ^ 2 / 10) := by
        gcongr; exact_mod_cast Nat.choose_le_pow n (hajosParam n)
    _ = Real.exp ((hajosParam n : ℝ) * Real.log (n : ℝ) +
          (-(hajosParam n : ℝ) ^ 2 / 10)) := by
        rw [pow_eq_exp_mul_log n hn' (hajosParam n), ← Real.exp_add]
    _ ≤ Real.exp (-(n : ℝ)) := by
        apply Real.exp_le_exp_of_le; linarith [hajosParam_sq_ge n]

/-- The union bound `subdivisionUnionBound n` tends to $0$ as $n \to \infty$. -/
theorem subdivision_union_bound_tendsto_zero :
    Tendsto subdivisionUnionBound atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards with n using subdivisionUnionBound_nonneg n
  · filter_upwards [subdivisionUnionBound_le_exp] with n hn using hn
  · exact tendsto_exp_neg_nat

/-- **Counterexample to Hajós's conjecture** (Theorem 5.3.2). If $\text{probKtSubdiv}(n)$
is the probability that $G(n, 1/2)$ contains a $K_t$-subdivision with $t = \lceil 10\sqrt n \rceil$,
and is dominated by the union bound, then it tends to $0$, giving a $K_t$-subdivision-free graph
of chromatic number $\Omega(n / \log n)$ asymptotically larger than $t$. -/
theorem hajos_conjecture_counterexample
    (probKtSubdiv : ℕ → ℝ)
    (hP_nonneg : ∀ n, 0 ≤ probKtSubdiv n)
    (hP_le : ∀ n, probKtSubdiv n ≤ subdivisionUnionBound n) :
    Tendsto probKtSubdiv atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds
    subdivision_union_bound_tendsto_zero
    hP_nonneg
    hP_le

end Hajos
