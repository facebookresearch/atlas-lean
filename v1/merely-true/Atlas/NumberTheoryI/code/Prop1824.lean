/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.StieltjesIntegral
import Mathlib.Analysis.Complex.Basic

namespace RiemannStieltjes

variable {a b : ℝ}

theorem stieltjesSum_linear_integrand {𝕜 : Type*} [NormedField 𝕜]
    (PT : TaggedPartition a b) (c₁ c₂ : 𝕜) (f₁ f₂ h : ℝ → 𝕜) :
    stieltjesSum PT (fun x => c₁ * f₁ x + c₂ * f₂ x) h =
    c₁ * stieltjesSum PT f₁ h + c₂ * stieltjesSum PT f₂ h := by
  simp only [stieltjesSum, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem stieltjesSum_linear_integrator {𝕜 : Type*} [NormedField 𝕜]
    (PT : TaggedPartition a b) (c₁ c₂ : 𝕜) (f g₁ g₂ : ℝ → 𝕜) :
    stieltjesSum PT f (fun x => c₁ * g₁ x + c₂ * g₂ x) =
    c₁ * stieltjesSum PT f g₁ + c₂ * stieltjesSum PT f g₂ := by
  simp only [stieltjesSum]
  trans (∑ k : Fin PT.n,
    (c₁ * (f (PT.tags k) * (g₁ (PT.pts ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) -
                              g₁ (PT.pts ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩))) +
     c₂ * (f (PT.tags k) * (g₂ (PT.pts ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) -
                              g₂ (PT.pts ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)))))
  · exact Finset.sum_congr rfl (fun k _ => by ring)
  · rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

lemma norm_linear_combo_sub {𝕜 : Type*} [NormedField 𝕜]
    (c₁ c₂ A B S₁ S₂ : 𝕜) :
    ‖c₁ * A + c₂ * B - (c₁ * S₁ + c₂ * S₂)‖ ≤
    ‖c₁‖ * ‖A - S₁‖ + ‖c₂‖ * ‖B - S₂‖ := by
  have : c₁ * A + c₂ * B - (c₁ * S₁ + c₂ * S₂) =
      c₁ * (A - S₁) + c₂ * (B - S₂) := by ring
  rw [this]
  calc ‖c₁ * (A - S₁) + c₂ * (B - S₂)‖
      ≤ ‖c₁ * (A - S₁)‖ + ‖c₂ * (B - S₂)‖ := norm_add_le _ _
    _ = ‖c₁‖ * ‖A - S₁‖ + ‖c₂‖ * ‖B - S₂‖ := by rw [norm_mul, norm_mul]

lemma eps_bound {𝕜 : Type*} [NormedField 𝕜] (c₁ c₂ : 𝕜) (ε : ℝ) (hε : 0 < ε) :
    (‖c₁‖ + ‖c₂‖) * (ε / (2 * (‖c₁‖ + ‖c₂‖ + 1))) < ε := by
  have hden : (0 : ℝ) < 2 * (‖c₁‖ + ‖c₂‖ + 1) := by positivity
  have h : ‖c₁‖ + ‖c₂‖ < 2 * (‖c₁‖ + ‖c₂‖ + 1) := by
    nlinarith [norm_nonneg c₁, norm_nonneg c₂]
  calc (‖c₁‖ + ‖c₂‖) * (ε / (2 * (‖c₁‖ + ‖c₂‖ + 1)))
      < 2 * (‖c₁‖ + ‖c₂‖ + 1) * (ε / (2 * (‖c₁‖ + ‖c₂‖ + 1))) :=
        mul_lt_mul_of_pos_right h (div_pos hε hden)
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hden)

lemma refinement_trans {PT : TaggedPartition a b}
    {R P : IntervalPartition a b}
    (hPT : PT.toIntervalPartition.IsRefinementOf R)
    (hR : R.IsRefinementOf P) :
    PT.toIntervalPartition.IsRefinementOf P := by
  intro j
  obtain ⟨i, hi⟩ := hR j
  obtain ⟨i', hi'⟩ := hPT ⟨i, by omega⟩
  exact ⟨i', by rw [hi', hi]⟩

theorem abel_summation_tagged_partitions {𝕜 : Type*} [NormedField 𝕜]
    (P : IntervalPartition a b) (f g : ℝ → 𝕜) :
    ∃ (PT_L PT_R : TaggedPartition a b),
      PT_L.toIntervalPartition.IsRefinementOf P ∧
      PT_R.toIntervalPartition.IsRefinementOf P ∧
      stieltjesSum PT_L f g + stieltjesSum PT_R g f = f b * g b - f a * g a := by

  let PT_L : TaggedPartition a b :=
    { n := P.n
      hn := P.hn
      pts := P.pts
      first := P.first
      last := P.last
      strict_mono := P.strict_mono
      tags := fun k => P.pts ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
      tag_mem := fun k =>
        ⟨le_refl _, le_of_lt (P.strict_mono (Fin.mk_lt_mk.mpr (by omega)))⟩ }

  let PT_R : TaggedPartition a b :=
    { n := P.n
      hn := P.hn
      pts := P.pts
      first := P.first
      last := P.last
      strict_mono := P.strict_mono
      tags := fun k => P.pts ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
      tag_mem := fun k =>
        ⟨le_of_lt (P.strict_mono (Fin.mk_lt_mk.mpr (by omega))), le_refl _⟩ }
  refine ⟨PT_L, PT_R, ?_, ?_, ?_⟩

  · intro j; exact ⟨j, rfl⟩

  · intro j; exact ⟨j, rfl⟩

  ·

    set h : ℕ → 𝕜 := fun i =>
      if hi : i < P.n + 1 then f (P.pts ⟨i, hi⟩) * g (P.pts ⟨i, hi⟩) else 0 with hh_def

    suffices ∑ k : Fin P.n, (h (k.val + 1) - h k.val) = f b * g b - f a * g a by
      simp only [stieltjesSum]
      rw [← Finset.sum_add_distrib]
      convert this using 1
      apply Finset.sum_congr rfl
      intro k _
      simp only [hh_def, show k.val + 1 < P.n + 1 from Nat.succ_lt_succ k.isLt,
        show k.val < P.n + 1 from Nat.lt_succ_of_lt k.isLt, dite_true]
      ring

    have hrange : (∑ k : Fin P.n, (h (↑k + 1) - h ↑k)) =
        ∑ i ∈ Finset.range P.n, (h (i + 1) - h i) := by
      rw [← Fin.sum_univ_eq_sum_range]
    rw [hrange, Finset.sum_range_sub]
    simp only [hh_def, show P.n < P.n + 1 from Nat.lt_succ_iff.mpr le_rfl,
      show 0 < P.n + 1 from Nat.zero_lt_succ P.n, dite_true]
    rw [P.last, P.first]



end RiemannStieltjes
