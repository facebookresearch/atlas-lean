/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open scoped ZeroAtInfty Convolution SchwartzMap ContDiff
open MeasureTheory Filter Topology Function Set TestFunctions
open ContinuousLinearMap

noncomputable section

namespace ConvolutionSmooth

/-- The complex multiplication bilinear map `ℂ × ℂ → ℂ` viewed as an `ℝ`-bilinear
continuous map; used as the bilinear pairing for convolutions in this file. -/
abbrev mulBilin : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ

/-- The convolution `v ⋆ ψ` of a `C₀` function `v` (continuous, vanishing at infinity)
with a Schwartz function `ψ`, as a function on Euclidean space. -/
def c0ConvSchwartz {n : ℕ} (v : C₀(EuclideanSpace ℝ (Fin n), ℂ))
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : EuclideanSpace ℝ (Fin n) → ℂ :=
  (v : EuclideanSpace ℝ (Fin n) → ℂ) ⋆[mulBilin] (ψ : EuclideanSpace ℝ (Fin n) → ℂ)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- The convolution of a bounded continuous function `v` with a Schwartz function `ψ`,
using a bilinear pairing `L`, is differentiable, and its Fréchet derivative is the
convolution of `v` with the derivative `fderiv ψ`. Step toward Melrose's Prop. 8.1. -/
theorem hasFDerivAt_convolution_bdd_schwartz
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : ℂ →L[ℝ] F →L[ℝ] G)
    (v : EuclideanSpace ℝ (Fin n) → ℂ) (hv_bdd : BddAbove (range fun x => ‖v x‖))
    (hv_cont : Continuous v) (ψ : 𝓢(EuclideanSpace ℝ (Fin n), F))
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (v ⋆[L] (ψ : EuclideanSpace ℝ (Fin n) → F))
      ((v ⋆[L.precompR (EuclideanSpace ℝ (Fin n))]
        (fun y => fderiv ℝ (ψ : EuclideanSpace ℝ (Fin n) → F) y)) x₀) x₀ := by
  let E := EuclideanSpace ℝ (Fin n)
  let L' := L.precompR E
  let ψ' : 𝓢(E, E →L[ℝ] F) := SchwartzMap.fderivCLM ℝ E F ψ
  obtain ⟨M, hM_pos, hM⟩ : ∃ M, 0 ≤ M ∧ ∀ x, ‖v x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hv_bdd
    exact ⟨max M 0, le_max_right _ _, fun x => (hM ⟨x, rfl⟩).trans (le_max_left _ _)⟩
  have hLM : 0 ≤ ‖L‖ * M := mul_nonneg L.opNorm_nonneg hM_pos

  set p := (volume : Measure E).integrablePower
  have peetre_bound : ∀ (V : Type _) [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : 𝓢(E, V)), ∃ Cf, 0 ≤ Cf ∧
      (∀ x ∈ Metric.ball x₀ 1, ∀ t : E, ‖(f : E → V) (x - t)‖ ≤ Cf / (1 + ‖t‖) ^ p) ∧
      Integrable (fun t : E => Cf / (1 + ‖t‖) ^ p) volume := by
    intro V _ _ f
    set Sf := (2 : ℝ) ^ p *
      ((Finset.Iic (p, (0 : ℕ))).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
    have hSf : ∀ z : E, (1 + ‖z‖) ^ p * ‖(f : E → V) z‖ ≤ Sf := by
      intro z; have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (p, 0))
        (le_refl p) (Nat.zero_le _) f z; simpa [iteratedFDeriv_zero_apply] using this
    have hSf_nn : 0 ≤ Sf := le_trans (by positivity) (hSf 0)
    refine ⟨Sf * (2 + ‖x₀‖) ^ p, mul_nonneg hSf_nn (by positivity), ?_, ?_⟩
    · intro x hx t
      have hxt_pos : (0 : ℝ) < (1 + ‖x - t‖) ^ p := by positivity
      have ht_pos : (0 : ℝ) < (1 + ‖t‖) ^ p := by positivity
      have h1 : 1 + ‖t‖ ≤ (1 + ‖x - t‖) * (1 + ‖x‖) := by
        have : ‖t‖ ≤ ‖x - t‖ + ‖x‖ := by
          calc ‖t‖ = ‖x - (x - t)‖ := by rw [sub_sub_cancel]
            _ ≤ ‖x‖ + ‖x - t‖ := norm_sub_le _ _
            _ = ‖x - t‖ + ‖x‖ := add_comm _ _
        nlinarith [norm_nonneg (x - t), norm_nonneg x]
      have h2 : 1 + ‖x‖ ≤ 2 + ‖x₀‖ := by
        have hd : ‖x - x₀‖ < 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hx
        have : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
          calc ‖x‖ = ‖x₀ + (x - x₀)‖ := by rw [add_sub_cancel]
            _ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
        linarith
      rw [le_div_iff₀ ht_pos]
      calc ‖(f : E → V) (x - t)‖ * (1 + ‖t‖) ^ p
          ≤ (Sf / (1 + ‖x - t‖) ^ p) * ((1 + ‖x - t‖) ^ p * (2 + ‖x₀‖) ^ p) := by
            apply mul_le_mul
            · rw [le_div_iff₀ hxt_pos, mul_comm]; exact hSf (x - t)
            · rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity)
                (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))) p
            · positivity
            · exact div_nonneg hSf_nn hxt_pos.le
        _ = Sf * (2 + ‖x₀‖) ^ p := by field_simp
    · exact ((Measure.integrable_pow_neg_integrablePower volume).congr
        (ae_of_all _ fun t => by
          simp only [p]; rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + ‖t‖),
            Real.rpow_natCast])).const_mul _
  obtain ⟨C₀, hC₀_nn, hC₀_bd, hC₀_int⟩ := peetre_bound F ψ
  obtain ⟨C₁, hC₁_nn, hC₁_bd, hC₁_int⟩ := peetre_bound (E →L[ℝ] F) ψ'
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds x₀ one_pos)
  · exact Eventually.of_forall fun x =>
      hv_cont.aestronglyMeasurable.convolution_integrand_snd L ψ.continuous.aestronglyMeasurable x
  · exact (hC₀_int.const_mul (‖L‖ * M)).mono'
      (hv_cont.aestronglyMeasurable.convolution_integrand_snd L ψ.continuous.aestronglyMeasurable x₀)
      (ae_of_all _ fun t => by
        calc ‖L (v t) ((ψ : E → F) (x₀ - t))‖
            ≤ ‖L‖ * ‖v t‖ * ‖(ψ : E → F) (x₀ - t)‖ := L.le_opNorm₂ _ _
          _ ≤ ‖L‖ * M * ‖(ψ : E → F) (x₀ - t)‖ := by gcongr; exact hM t
          _ ≤ ‖L‖ * M * (C₀ / (1 + ‖t‖) ^ p) := by
              gcongr; exact hC₀_bd x₀ (Metric.mem_ball_self one_pos) t)
  · exact hv_cont.aestronglyMeasurable.convolution_integrand_snd L'
      ψ'.continuous.aestronglyMeasurable x₀
  · filter_upwards with t x hx
    have fderiv_eq := (SchwartzMap.fderivCLM_apply ℝ ψ (x - t)).symm
    calc ‖L' (v t) (fderiv ℝ (ψ : E → F) (x - t))‖
        = ‖(L (v t)).comp (fderiv ℝ (ψ : E → F) (x - t))‖ := rfl
      _ ≤ ‖L (v t)‖ * ‖fderiv ℝ (ψ : E → F) (x - t)‖ := opNorm_comp_le _ _
      _ ≤ (‖L‖ * M) * ‖(ψ' : E → E →L[ℝ] F) (x - t)‖ := by
          rw [fderiv_eq]; gcongr
          calc ‖L (v t)‖ ≤ ‖L‖ * ‖v t‖ := L.le_opNorm _
            _ ≤ ‖L‖ * M := by gcongr; exact hM t
      _ ≤ (‖L‖ * M) * (C₁ / (1 + ‖t‖) ^ p) := by gcongr; exact hC₁_bd x hx t
      _ = ‖L‖ * M * (C₁ / (1 + ‖t‖) ^ p) := by ring
  · exact (hC₁_int.const_mul (‖L‖ * M)).congr (ae_of_all _ fun t => by ring)
  · filter_upwards with t x _
    exact (L (v t)).hasFDerivAt.comp x
      ((ψ.hasFDerivAt (x - t)).comp x
        ((hasFDerivAt_id (𝕜 := ℝ) x).sub (hasFDerivAt_const t x))
        |>.congr_fderiv (by ext; simp))


set_option maxHeartbeats 800000 in
/-- The convolution of a bounded continuous function `v` with a Schwartz function `ψ`,
using a bilinear pairing `L`, is `Cᵏ` for every `k : ℕ`. Iterates the FDeriv lemma. -/
theorem contDiff_convolution_bdd_schwartz
    {n : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : ℂ →L[ℝ] F →L[ℝ] G)
    (v : EuclideanSpace ℝ (Fin n) → ℂ)
    (hv_bdd : BddAbove (range fun x => ‖v x‖))
    (hv_cont : Continuous v)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), F))
    (k : ℕ) :
    ContDiff ℝ k (v ⋆[L] (ψ : EuclideanSpace ℝ (Fin n) → F)) := by
  induction k generalizing F G with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact hv_bdd.continuous_convolution_left_of_integrable L hv_cont ψ.integrable
  | succ k ih =>
    simp only [Nat.cast_add, Nat.cast_one] at *
    rw [contDiff_succ_iff_hasFDerivAt]
    let E := EuclideanSpace ℝ (Fin n)

    let ψ' : 𝓢(E, E →L[ℝ] F) := SchwartzMap.fderivCLM ℝ E F ψ
    refine ⟨fun x₀ => (v ⋆[L.precompR E] (ψ' : E → E →L[ℝ] F)) x₀, ?_, ?_⟩
    ·
      exact ih (L.precompR E) ψ'
    ·
      intro x₀
      have key := hasFDerivAt_convolution_bdd_schwartz L v hv_bdd hv_cont ψ x₀


      convert key using 1

/-- The convolution of a `C₀` function `v` with a Schwartz function `ψ` is `Cᵏ` for every
`k : ℕ`. Specialisation of `contDiff_convolution_bdd_schwartz` to `mulBilin`. -/
theorem convolution_c0_schwartz_contDiff
    {n : ℕ}
    (v : C₀(EuclideanSpace ℝ (Fin n), ℂ))
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (k : ℕ) :
    ContDiff ℝ k (c0ConvSchwartz v ψ) :=
  contDiff_convolution_bdd_schwartz mulBilin (v : EuclideanSpace ℝ (Fin n) → ℂ)
    ⟨‖v.toBCF‖, by rintro _ ⟨x, rfl⟩; exact v.toBCF.norm_coe_le_norm x⟩
    v.continuous ψ k


/-- Translation `x ↦ x - t` is a proper map on a finite-dimensional normed space, so it
pushes the cocompact filter to itself. -/
lemma tendsto_sub_cocompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (t : E) :
    Tendsto (· - t) (cocompact E) (cocompact E) :=
  (Homeomorph.subRight t).isClosedEmbedding.tendsto_cocompact


/-- The cocompact filter on `EuclideanSpace ℝ (Fin d)` is countably generated, with a
basis of complements of closed balls of integer radii. -/
instance cocompact_isCountablyGenerated (d : ℕ) :
    (cocompact (EuclideanSpace ℝ (Fin d))).IsCountablyGenerated := by
  apply HasCountableBasis.isCountablyGenerated (ι := ℕ) (p := fun _ => True)
    (s := fun k => (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) k)ᶜ)
  exact ⟨⟨fun s => ⟨fun hs => by
    rw [mem_cocompact] at hs; obtain ⟨K, hK, hKs⟩ := hs
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    exact ⟨⌈R⌉₊, trivial, fun x hx => by
      apply hKs; intro hxK
      have h2 : (⌈R⌉₊ : ℝ) < dist x 0 := by
        rwa [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hx
      linarith [Nat.le_ceil R, Metric.mem_closedBall.mp (hR hxK)]⟩,
    fun ⟨k, _, hk⟩ => mem_cocompact.mpr ⟨_, isCompact_closedBall 0 k, hk⟩⟩⟩,
    countable_univ.to_subtype⟩


set_option maxHeartbeats 800000 in
/-- If a bounded continuous function `v` vanishes at infinity, then its convolution with a
Schwartz function `ψ` (via a bilinear pairing `L`) vanishes at infinity. -/
theorem tendsto_convolution_bdd_schwartz_zero {n : ℕ}
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : ℂ →L[ℝ] F →L[ℝ] G)
    (v : EuclideanSpace ℝ (Fin n) → ℂ)
    (hv_bdd : BddAbove (range fun x => ‖v x‖))
    (hv_cont : Continuous v)
    (hv_zero : Tendsto v (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0))
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), F)) :
    Tendsto (v ⋆[L] (ψ : EuclideanSpace ℝ (Fin n) → F))
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
  let E := EuclideanSpace ℝ (Fin n)
  rw [← convolution_flip L]
  obtain ⟨M, hM⟩ := hv_bdd
  rw [← integral_zero E G]
  apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖L.flip‖ * M * ‖(ψ : E → F) t‖)
  · apply Eventually.of_forall; intro x
    exact (L.flip.continuous₂.comp₂ ψ.continuous
      (hv_cont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · apply Eventually.of_forall; intro x
    apply Eventually.of_forall; intro t
    calc ‖L.flip ((ψ : E → F) t) (v (x - t))‖
        ≤ ‖L.flip‖ * ‖(ψ : E → F) t‖ * ‖v (x - t)‖ := L.flip.le_opNorm₂ _ _
      _ ≤ ‖L.flip‖ * ‖(ψ : E → F) t‖ * M := by gcongr; exact hM ⟨x - t, rfl⟩
      _ = ‖L.flip‖ * M * ‖(ψ : E → F) t‖ := by ring
  · exact (ψ.integrable.norm).const_mul _
  · apply Eventually.of_forall; intro t
    have hv_sub : Tendsto (fun x => v (x - t)) (cocompact E) (𝓝 0) :=
      hv_zero.comp (tendsto_sub_cocompact t)
    rw [← map_zero (L.flip ((ψ : E → F) t))]
    exact (L.flip ((ψ : E → F) t)).continuous.continuousAt.tendsto.comp hv_sub


set_option maxHeartbeats 1600000 in
/-- Every iterated Fréchet derivative of the convolution `v ⋆ ψ` (for `v` bounded
continuous, vanishing at infinity, and `ψ` Schwartz) tends to zero at infinity. -/
theorem iteratedFDeriv_convolution_bdd_schwartz_zeroAtInfty {n : ℕ}
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : ℂ →L[ℝ] F →L[ℝ] G)
    (v : EuclideanSpace ℝ (Fin n) → ℂ)
    (hv_bdd : BddAbove (range fun x => ‖v x‖))
    (hv_cont : Continuous v)
    (hv_zero : Tendsto v (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0))
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), F))
    (m : ℕ) :
    Tendsto (fun x => ‖iteratedFDeriv ℝ m (v ⋆[L] (ψ : EuclideanSpace ℝ (Fin n) → F)) x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
  let E := EuclideanSpace ℝ (Fin n)
  induction m generalizing F G with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, comp_apply]
    rw [show (fun x => ‖(continuousMultilinearCurryFin0 ℝ E G).symm
        ((v ⋆[L] (ψ : E → F)) x)‖) =
      (fun x => ‖(v ⋆[L] (ψ : E → F)) x‖) from by
        ext x; simp]
    exact tendsto_zero_iff_norm_tendsto_zero.mp
      (tendsto_convolution_bdd_schwartz_zero L v hv_bdd hv_cont hv_zero ψ)
  | succ m ih =>

    have norm_eq : ∀ x : E, ‖iteratedFDeriv ℝ (m + 1) (v ⋆[L] (ψ : E → F)) x‖ =
        ‖iteratedFDeriv ℝ m (fderiv ℝ (v ⋆[L] (ψ : E → F))) x‖ :=
      fun x => norm_iteratedFDeriv_fderiv.symm
    simp_rw [norm_eq]

    let ψ' : 𝓢(E, E →L[ℝ] F) := SchwartzMap.fderivCLM ℝ E F ψ
    have hfderiv : fderiv ℝ (v ⋆[L] (ψ : E → F)) =
        (v ⋆[L.precompR E] (ψ' : E → E →L[ℝ] F)) := by
      ext x
      have hfd := hasFDerivAt_convolution_bdd_schwartz L v hv_bdd hv_cont ψ x
      rw [hfd.fderiv]
      congr
    simp_rw [hfderiv]
    exact ih (L.precompR E) ψ'


/-- Every iterated derivative of the convolution `v ⋆ ψ` of a `C₀` function `v` with a
Schwartz function `ψ` tends to zero at infinity. -/
theorem convolution_c0_schwartz_iteratedFDeriv_zeroAtInfty
    {n : ℕ}
    (v : C₀(EuclideanSpace ℝ (Fin n), ℂ))
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (m : ℕ) :
    Tendsto (fun x => ‖iteratedFDeriv ℝ m (c0ConvSchwartz v ψ) x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) :=
  iteratedFDeriv_convolution_bdd_schwartz_zeroAtInfty mulBilin
    (v : EuclideanSpace ℝ (Fin n) → ℂ)
    ⟨‖v.toBCF‖, by rintro _ ⟨x, rfl⟩; exact v.toBCF.norm_coe_le_norm x⟩
    v.continuous
    v.zero_at_infty'
    ψ m

variable {n : ℕ}

end ConvolutionSmooth

end
