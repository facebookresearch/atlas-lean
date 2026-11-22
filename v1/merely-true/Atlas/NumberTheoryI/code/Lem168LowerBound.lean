/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open MeasureTheory Filter Topology Set

set_option maxHeartbeats 800000

lemma integrableOn_g_Ioc (f : ℝ → ℝ) (hf_mono : Monotone f) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun t => (f t - t) / t ^ 2) (Ioc a b) := by
  have hfm : Measurable (fun t : ℝ => (f t - t) / t ^ 2) :=
    (hf_mono.measurable.sub measurable_id).div (measurable_id.pow_const 2)
  refine IntegrableOn.of_bound
    (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
    (hf := hfm.aestronglyMeasurable.restrict)
    (C := (|f a| + |f b| + b) / a ^ 2) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  apply ae_of_all; intro t ht
  have hta : a ≤ t := le_of_lt ht.1
  have htb : t ≤ b := ht.2
  have ht_pos : 0 < t := lt_of_lt_of_le ha hta
  simp only [Real.norm_eq_abs]
  rw [abs_div, abs_pow, abs_of_pos ht_pos]
  have hfa : f a ≤ f t := hf_mono hta
  have hfb : f t ≤ f b := hf_mono htb
  have hnum : |f t - t| ≤ |f a| + |f b| + b := by
    rcases le_or_gt (f t) t with h | h
    · rw [abs_of_nonpos (by linarith)]
      linarith [abs_nonneg (f b), neg_abs_le (f a)]
    · rw [abs_of_pos (by linarith)]
      linarith [abs_nonneg (f a), le_abs_self (f b)]
  have hdenom : a ^ 2 ≤ t ^ 2 := sq_le_sq' (by linarith) hta
  calc |f t - t| / t ^ 2
      ≤ |f t - t| / a ^ 2 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos ha) hdenom
      _ ≤ (|f a| + |f b| + b) / a ^ 2 :=
        div_le_div_of_nonneg_right hnum (le_of_lt (sq_pos_of_pos ha))

lemma setIntegral_Ioc_split (g : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hg1 : IntegrableOn g (Ioc a b)) (hg2 : IntegrableOn g (Ioc b c)) :
    ∫ t in Ioc a c, g t = (∫ t in Ioc a b, g t) + ∫ t in Ioc b c, g t := by
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc]
  exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hg1 hg2
