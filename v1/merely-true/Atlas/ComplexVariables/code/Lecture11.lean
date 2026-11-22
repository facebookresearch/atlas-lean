/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.Order

open Complex Filter Set Topology Metric

lemma meromorphicAt_of_differentiableAt_punctured_bounded {f : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (hb : ∀ᶠ z in 𝓝[≠] c, ‖f z‖ ≤ M) :
    MeromorphicAt f c := by

  have hbnd : IsBoundedUnder (· ≤ ·) (𝓝[≠] c) fun z => ‖f z - f c‖ := by
    refine ⟨M + ‖f c‖, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hb] with z hz
    calc ‖f z - f c‖ ≤ ‖f z‖ + ‖f c‖ := norm_sub_le _ _
      _ ≤ M + ‖f c‖ := by linarith

  have htend := tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd hbnd
  set L := (𝓝[≠] c).limUnder f

  have hcont : ContinuousAt (Function.update f c L) c :=
    continuousAt_update_same.mpr htend

  have hd' : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ (Function.update f c L) z := by
    filter_upwards [hd, self_mem_nhdsWithin] with z hdz hzc
    simp only [mem_compl_iff, mem_singleton_iff] at hzc
    exact hdz.congr_of_eventuallyEq <| by
      filter_upwards [isOpen_compl_singleton.mem_nhds hzc] with w hw
      exact Function.update_of_ne hw L f

  have hanalytic :=
    analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd' hcont

  exact hanalytic.meromorphicAt.congr (by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact Function.update_of_ne (mem_compl_singleton_iff.mp hz) L f)

theorem casorati_weierstrass {f : ℂ → ℂ} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (hnotmero : ¬ MeromorphicAt f c)
    (w : ℂ) (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ z : ℂ, 0 < ‖z - c‖ ∧ ‖z - c‖ < δ ∧ ‖f z - w‖ < ε := by

  by_contra h
  push Not at h


  set g : ℂ → ℂ := fun z => (f z - w)⁻¹

  have key : ∀ z : ℂ, z ≠ c → dist z c < δ → ε ≤ ‖f z - w‖ := fun z hzc hzd =>
    h z (by rwa [norm_pos_iff, sub_ne_zero]) (by rwa [dist_eq_norm] at hzd)

  have hfne : ∀ z : ℂ, z ≠ c → dist z c < δ → f z - w ≠ 0 := by
    intro z hzc hzd habs
    have := key z hzc hzd
    rw [habs, norm_zero] at this
    linarith

  have hg_diff : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ g z := by
    filter_upwards [hd, eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds c hδ),
                     self_mem_nhdsWithin] with z hz_diff hz_ball hz_ne
    simp only [mem_compl_iff, mem_singleton_iff] at hz_ne
    exact (hz_diff.sub (differentiableAt_const w)).inv (hfne z hz_ne hz_ball)

  have hg_bnd : ∀ᶠ z in 𝓝[≠] c, ‖g z‖ ≤ ε⁻¹ := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds c hδ),
                     self_mem_nhdsWithin] with z hz_ball hz_ne
    simp only [mem_compl_iff, mem_singleton_iff] at hz_ne
    simp only [g, norm_inv]
    exact inv_anti₀ hε (key z hz_ne hz_ball)

  have hg_mero := meromorphicAt_of_differentiableAt_punctured_bounded hg_diff hg_bnd

  exact hnotmero <| ((MeromorphicAt.const w c).add hg_mero.inv).congr (by
    filter_upwards [self_mem_nhdsWithin] with z hzc
    simp only [mem_compl_iff, mem_singleton_iff] at hzc
    simp [g, inv_inv])
