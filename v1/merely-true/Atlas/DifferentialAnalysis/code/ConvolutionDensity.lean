/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.ConvolutionDensityFix
import Atlas.DifferentialAnalysis.code.TestFunctions
import Atlas.DifferentialAnalysis.code.SchwartzCutoffConvergence
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

open scoped ZeroAtInfty Convolution
open MeasureTheory Filter Topology Function Set TestFunctions

noncomputable section

namespace ConvolutionDensity

/-- The cocompact filter on Euclidean space is countably generated: it has a
countable basis given by complements of closed balls of integer radius. -/
instance cocompact_eucl_countablyGenerated {n : ℕ} :
    (Filter.cocompact (EuclideanSpace ℝ (Fin n))).IsCountablyGenerated := by
  apply Filter.HasCountableBasis.isCountablyGenerated (ι := ℕ)
    (p := fun _ => True)
    (s := fun m => (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) m)ᶜ)
  exact {
    countable := Set.countable_univ.mono (fun _ _ => trivial)
    toHasBasis := {
      mem_iff' := by
        intro S; simp only [true_and]
        constructor
        · intro hS
          rw [Filter.mem_cocompact] at hS
          obtain ⟨K, hK, hKS⟩ := hS
          obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
          obtain ⟨m, hm⟩ := exists_nat_ge r
          exact ⟨m, fun x hx => hKS fun hxK => by
            simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hx
            exact absurd (le_trans (hr hxK) hm) (not_le.mpr hx)⟩
        · rintro ⟨m, hm⟩
          exact Filter.mem_cocompact.mpr
            ⟨Metric.closedBall 0 m, isCompact_closedBall 0 m, hm⟩
    }
  }

/-- Approximate-identity convergence for `C₀` functions: if `φ i` is a family
of nonnegative, integral-one functions whose supports shrink to `{0}`, then
the convolutions `φ i ⋆ f` converge uniformly to `f` for any `f ∈ C₀(G, ℝ)`.
This is a key ingredient for proving density results via mollification. -/
theorem approxIdentity_tendstoUniformly
    {G : Type*} [SeminormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddLeftInvariant] [SFinite μ]
    {ι : Type*} {l : Filter ι}
    {φ : ι → G → ℝ}
    (f : C₀(G, ℝ))
    (hnφ : ∀ᶠ i in l, ∀ x, 0 ≤ φ i x)
    (hiφ : ∀ᶠ i in l, ∫ x, φ i x ∂μ = 1)
    (hφ : Tendsto (fun i => support (φ i)) l (𝓝 (0 : G)).smallSets)
    (hmφ : ∀ᶠ i in l, AEStronglyMeasurable (φ i) μ) :
    TendstoUniformly (fun i => (φ i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
      (f : G → ℝ))) (f : G → ℝ) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have huc := ZeroAtInftyContinuousMap.uniformContinuous f
  rw [Metric.uniformContinuous_iff] at huc
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  obtain ⟨δ, hδ, hfδ⟩ := huc (ε / 2) hε2
  rw [tendsto_smallSets_iff] at hφ
  have hφδ := hφ (Metric.ball 0 δ) (Metric.ball_mem_nhds 0 hδ)
  filter_upwards [hnφ, hiφ, hφδ, hmφ] with i hnφi hiφi hφi hmφi
  intro x
  rw [dist_comm]
  calc dist ((φ i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
        (f : G → ℝ)) x) (f x)
      ≤ ε / 2 := dist_convolution_le hε2.le hφi hnφi hiφi
        (map_continuous f).aestronglyMeasurable
        (fun y hy => le_of_lt (hfδ (Metric.mem_ball.mp hy)))
    _ < ε := half_lt_self hε



/-- Mollification threshold in the `C^k` norm: for any compactly-supported
`C^k` function `v` and any `ε > 0`, there exists a radius `r > 0` such that
convolution with any normalised bump of outer radius at most `r` approximates
`v` within `ε` in the `C^k` norm. The proof proceeds by induction on `k`,
using uniform continuity of derivatives at the base step and commuting
convolution with `fderiv` at the inductive step. -/
lemma ckNorm_convolution_threshold
    {n : ℕ} (k : ℕ) (v : EuclideanSpace ℝ (Fin n) → ℂ)
    (hv_supp : HasCompactSupport v) (hv_smooth : ContDiff ℝ k v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ ψ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)),
      ψ.rOut ≤ r →
      ckNorm n k (fun x => v x -
        (ψ.normed (volume : Measure (EuclideanSpace ℝ (Fin n)))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x) < ε := by
  induction k generalizing v ε with
  | zero =>
    have hv_cont := hv_smooth.continuous
    obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.mp
      (hv_supp.uniformContinuous_of_continuous hv_cont) (ε / 2) (by linarith)
    refine ⟨δ, hδ, fun ψ hψ => ?_⟩
    show ⨆ x, ‖v x - _‖ < ε
    calc ⨆ x, ‖v x - (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x‖
        ≤ ε / 2 := ciSup_le fun x₀ => by
          rw [← dist_eq_norm, dist_comm]
          exact ψ.dist_normed_convolution_le hv_cont.aestronglyMeasurable fun y hy =>
            (hfδ (lt_of_lt_of_le (Metric.mem_ball.mp hy) hψ)).le
      _ < ε := by linarith
  | succ k ih =>
    have hv_cont := hv_smooth.continuous
    have hv_k : ContDiff ℝ k v := hv_smooth.of_le (by exact_mod_cast Nat.le_succ k)
    set m := (1 : ℝ) + ↑n
    have hm : 0 < m := by positivity
    have hε' : 0 < ε / m := div_pos hε hm
    obtain ⟨r₀, hr₀, h₀⟩ := ih v hv_supp hv_k (ε / m) hε'
    have hDj : ∀ j : Fin n,
        ∃ rj : ℝ, 0 < rj ∧ ∀ ψ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)),
          ψ.rOut ≤ rj →
          ckNorm n k (fun x => fderiv ℝ v x (EuclideanSpace.single j 1) -
            (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (fun y => fderiv ℝ v y (EuclideanSpace.single j 1))) x) < ε / m := by
      intro j
      have hDj_supp : HasCompactSupport (fun x => fderiv ℝ v x (EuclideanSpace.single j 1)) := by
        change HasCompactSupport ((fun L : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ) =>
          L (EuclideanSpace.single j 1)) ∘ fderiv ℝ v)
        exact (hv_supp.fderiv ℝ).comp_left (by simp)
      have hDj_smooth : ContDiff ℝ k (fun x => fderiv ℝ v x (EuclideanSpace.single j 1)) :=
        (hv_smooth.fderiv_right (m := k)
          (by exact_mod_cast Nat.lt_succ_of_le le_rfl)).clm_apply contDiff_const
      exact ih _ hDj_supp hDj_smooth (ε / m) hε'

    choose rj hrj_pos hrj using hDj

    by_cases hn : n = 0
    ·
      subst hn
      refine ⟨r₀, hr₀, fun ψ hψ => ?_⟩
      simp only [ckNorm, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      have := h₀ ψ hψ
      simp only [m, Nat.cast_zero, add_zero, div_one] at this
      exact this
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn

      haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
      set r := min r₀ (Finset.univ.inf' Finset.univ_nonempty rj)

      have hr_pos : 0 < r := lt_min hr₀ (by
        simp only [Finset.lt_inf'_iff]; exact fun j _ => hrj_pos j)
      have hψ_rj : ∀ (ψ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))), ψ.rOut ≤ r →
          ∀ j : Fin n, ψ.rOut ≤ rj j := fun ψ hψ j =>
        le_trans hψ (le_trans (min_le_right _ _) (Finset.inf'_le _ (Finset.mem_univ j)))
      refine ⟨r, hr_pos, fun ψ hψ => ?_⟩
      show ckNorm n (k + 1) _ < ε
      simp only [ckNorm]
      have hψ_r₀ : ψ.rOut ≤ r₀ := le_trans hψ (min_le_left _ _)
      have h_main := h₀ ψ hψ_r₀
      have h_deriv : ∀ j : Fin n,
          ckNorm n k (fun x => fderiv ℝ (fun y => v y -
            (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y) x
            (EuclideanSpace.single j 1)) < ε / m := by
        intro j
        have hv_diff : Differentiable ℝ v := hv_smooth.differentiable (by
          show (↑(k + 1) : WithTop ℕ∞) ≠ 0; exact_mod_cast Nat.succ_ne_zero k)
        have hg_diff : Differentiable ℝ (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) :=
          (ψ.hasCompactSupport_normed.contDiff_convolution_left (n := ⊤)
            _ ψ.contDiff_normed hv_cont.locallyIntegrable).differentiable
              (by exact_mod_cast ENat.top_ne_zero)
        have heq : (fun x => fderiv ℝ (fun y => v y -
            (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y) x
            (EuclideanSpace.single j 1)) =
          (fun x => fderiv ℝ v x (EuclideanSpace.single j 1) -
            (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (fun y => fderiv ℝ v y (EuclideanSpace.single j 1))) x) := by
          ext x
          rw [show (fun y => v y - (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y) =
            v - (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) from rfl,
            fderiv_sub (hv_diff x) (hg_diff x), ContinuousLinearMap.sub_apply]
          congr 1
          have hf_loc : LocallyIntegrable (ψ.normed (volume : Measure (EuclideanSpace ℝ (Fin n)))) volume :=
            ψ.integrable_normed.locallyIntegrable
          have hv1 : ContDiff ℝ 1 v := hv_smooth.of_le (by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))
          rw [(hv_supp.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
            hf_loc hv1 x).fderiv]
          exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hf_loc (hv_supp.fderiv ℝ)
            (hv1.continuous_fderiv one_ne_zero) x (EuclideanSpace.single j 1)
        rw [heq]
        exact hrj j ψ (hψ_rj ψ hψ j)
      have h_sum : Finset.sum Finset.univ (fun j : Fin n =>
          ckNorm n k (fun x => fderiv ℝ (fun y => v y -
            (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y) x
            (EuclideanSpace.single j 1))) < ↑n * (ε / m) := by
        calc _ < Finset.sum Finset.univ (fun _ : Fin n => ε / m) :=
              Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => h_deriv j)
          _ = ↑(Fintype.card (Fin n)) * (ε / m) := by
              simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ = ↑n * (ε / m) := by simp [Fintype.card_fin]
      calc ckNorm n k (fun x => v x - _) +
            Finset.sum Finset.univ (fun j => ckNorm n k (fun x =>
              fderiv ℝ (fun y => v y - _) x (EuclideanSpace.single j 1)))
          < ε / m + ↑n * (ε / m) := by linarith
        _ = ε := by show ε / m + ↑n * (ε / m) = ε; field_simp [show m ≠ 0 from ne_of_gt hm]; ring

/-- Any compactly-supported `C^k` function on Euclidean space can be
approximated in the `C^k` norm by a Schwartz function. The approximant is
constructed by convolving `v` with a sufficiently narrow normalised bump,
which produces a compactly-supported smooth function — and hence a Schwartz
function — within `ε` of `v` in the `C^k` norm. -/
theorem approx_compactly_supported_Ck_by_schwartz
    {n : ℕ} (k : ℕ) (v : EuclideanSpace ℝ (Fin n) → ℂ)
    (hv_supp : HasCompactSupport v) (hv_smooth : ContDiff ℝ k v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      ckNorm n k (fun x => v x - φ x) < ε := by
  obtain ⟨r, hr, hbound⟩ := ckNorm_convolution_threshold k v hv_supp hv_smooth ε hε
  let ψ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨r / 2, r, by linarith, by linarith⟩
  set μ : Measure (EuclideanSpace ℝ (Fin n)) := volume
  set g := ψ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] v
  have hg_supp : HasCompactSupport g := ψ.hasCompactSupport_normed.convolution _ hv_supp
  have hg_smooth : ContDiff ℝ (↑⊤ : ℕ∞) g :=
    ψ.hasCompactSupport_normed.contDiff_convolution_left (n := ⊤) _
      ψ.contDiff_normed hv_smooth.continuous.locallyIntegrable
  refine ⟨hg_supp.toSchwartzMap hg_smooth, ?_⟩
  have hφ_eq : ∀ x, (hg_supp.toSchwartzMap hg_smooth : EuclideanSpace ℝ (Fin n) → ℂ) x = g x :=
    hg_supp.toSchwartzMap_toFun hg_smooth
  have : (fun x => v x - (hg_supp.toSchwartzMap hg_smooth) x) = (fun x => v x - g x) := by
    ext x; simp [hφ_eq]
  rw [this]
  exact hbound ψ le_rfl

/-- `CkNormBdd n k f` is the recursive predicate stating that all derivatives
of `f : EuclideanSpace ℝ (Fin n) → ℂ` up to order `k` are bounded; that is,
`f` is `k` times differentiable and `f` together with all its partial
derivatives up to order `k` have bounded norm ranges. -/
def CkNormBdd (n : ℕ) : ℕ → (EuclideanSpace ℝ (Fin n) → ℂ) → Prop
  | 0, f => BddAbove (Set.range fun x => ‖f x‖)
  | k + 1, f =>
    CkNormBdd n k f ∧
      Differentiable ℝ f ∧
      ∀ j : Fin n, CkNormBdd n k fun x => fderiv ℝ f x (EuclideanSpace.single j 1)





/-- Base case of the triangle inequality for the `C^k` norm: at order zero,
the supremum norm satisfies `‖f + g‖_∞ ≤ ‖f‖_∞ + ‖g‖_∞` whenever each is
bounded above. -/
lemma ckNorm_add_le_base {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : BddAbove (Set.range fun x => ‖f x‖))
    (hg : BddAbove (Set.range fun x => ‖g x‖)) :
    ckNorm n 0 (fun x => f x + g x) ≤ ckNorm n 0 f + ckNorm n 0 g := by
  show (⨆ x, ‖f x + g x‖) ≤ (⨆ x, ‖f x‖) + (⨆ x, ‖g x‖)
  apply ciSup_le
  intro x
  calc ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    _ ≤ (⨆ y, ‖f y‖) + (⨆ y, ‖g y‖) := by
        gcongr
        · exact le_ciSup hf x
        · exact le_ciSup hg x


/-- Triangle inequality for the `C^k` norm: for functions with bounded
derivatives up to order `k`, the `C^k` norm of a sum is at most the sum of
the `C^k` norms. Proved by induction on `k` using linearity of `fderiv` on
sums of differentiable functions. -/
theorem ckNorm_add_le
    {n : ℕ} (k : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : CkNormBdd n k f) (hg : CkNormBdd n k g) :
    ckNorm n k (fun x => f x + g x) ≤ ckNorm n k f + ckNorm n k g := by
  induction k generalizing f g with
  | zero => exact ckNorm_add_le_base f g hf hg
  | succ k ih =>
    simp only [ckNorm]
    have hf_bdd := hf.1
    have hf_diff := hf.2.1
    have hg_bdd := hg.1
    have hg_diff := hg.2.1

    have h_main := ih f g hf_bdd hg_bdd

    have h_sum : ∀ j : Fin n, ∀ x,
        fderiv ℝ (fun x => f x + g x) x (EuclideanSpace.single j 1) =
        fderiv ℝ f x (EuclideanSpace.single j 1) + fderiv ℝ g x (EuclideanSpace.single j 1) := by
      intro j x
      have : fderiv ℝ (fun x => f x + g x) x = fderiv ℝ f x + fderiv ℝ g x := by
        have : (fun x => f x + g x) = f + g := rfl
        rw [this, fderiv_add (hf_diff x) (hg_diff x)]
      rw [this, ContinuousLinearMap.add_apply]

    have h_deriv_sum : ∀ j : Fin n,
        ckNorm n k (fun x => fderiv ℝ (fun x => f x + g x) x (EuclideanSpace.single j 1)) ≤
        ckNorm n k (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) +
        ckNorm n k (fun x => fderiv ℝ g x (EuclideanSpace.single j 1)) := by
      intro j
      have heq : (fun x => fderiv ℝ (fun x => f x + g x) x (EuclideanSpace.single j 1)) =
          (fun x => fderiv ℝ f x (EuclideanSpace.single j 1) +
                    fderiv ℝ g x (EuclideanSpace.single j 1)) := by
        ext x; exact h_sum j x
      rw [heq]
      exact ih _ _ (hf.2.2 j) (hg.2.2 j)

    have h_sum_le : Finset.sum Finset.univ (fun j =>
          ckNorm n k (fun x => fderiv ℝ (fun x => f x + g x) x (EuclideanSpace.single j 1))) ≤
        Finset.sum Finset.univ (fun j =>
          ckNorm n k (fun x => fderiv ℝ f x (EuclideanSpace.single j 1))) +
        Finset.sum Finset.univ (fun j =>
          ckNorm n k (fun x => fderiv ℝ g x (EuclideanSpace.single j 1))) := by
      calc Finset.sum Finset.univ (fun j =>
              ckNorm n k (fun x => fderiv ℝ (fun x => f x + g x) x (EuclideanSpace.single j 1)))
        _ ≤ Finset.sum Finset.univ (fun j =>
              (ckNorm n k (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) +
               ckNorm n k (fun x => fderiv ℝ g x (EuclideanSpace.single j 1)))) := by
            gcongr with j _
            exact h_deriv_sum j
        _ = _ := Finset.sum_add_distrib
    linarith






section CompactSupportSchwartz

open scoped ContDiff

/-- Multiplication by a compactly-supported function on the left preserves
compact support. -/
theorem hasCompactSupport_mul_of_left {n : ℕ}
    (μ : EuclideanSpace ℝ (Fin n) → ℂ) (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hμ_cpt : HasCompactSupport μ) :
    HasCompactSupport (fun x => μ x * g x) :=
  hμ_cpt.mul_right

/-- The pointwise product of two smooth functions on Euclidean space is
smooth. -/
theorem contDiff_mul_of_both {n : ℕ}
    (μ : EuclideanSpace ℝ (Fin n) → ℂ) (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hμ_smooth : ContDiff ℝ ∞ μ) (hg_smooth : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => μ x * g x) :=
  hμ_smooth.mul hg_smooth

end CompactSupportSchwartz

end ConvolutionDensity

section CompactSupportDenseSchwartz

open Filter Topology SchwartzMap


end CompactSupportDenseSchwartz

section CutoffSchwartz

open SchwartzMap

set_option maxHeartbeats 3200000

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Multiplication of a Schwartz function `f` by a compactly-supported smooth
real-valued function `φ`. The result is again Schwartz with compact support
contained in the support of `φ`. -/
noncomputable def SchwartzMap.cutoffMul (φ : E → ℝ) (hφcs : HasCompactSupport φ)
    (hφcd : ContDiff ℝ ⊤ φ) (f : SchwartzMap E F) : SchwartzMap E F :=
  (hφcs.smul_right (f' := ⇑f)).toSchwartzMap
    ((hφcd.of_le le_top).smul f.smooth')

omit [FiniteDimensional ℝ E] in
/-- Pointwise evaluation of `SchwartzMap.cutoffMul`: at each `x`, the cut-off
product equals `φ x • f x`. -/
@[simp]
theorem SchwartzMap.cutoffMul_apply (φ : E → ℝ) (hφcs : HasCompactSupport φ)
    (hφcd : ContDiff ℝ ⊤ φ) (f : SchwartzMap E F) (x : E) :
    (SchwartzMap.cutoffMul φ hφcs hφcd f) x = φ x • f x := by
  simp [SchwartzMap.cutoffMul, HasCompactSupport.toSchwartzMap_toFun]

end CutoffSchwartz

end

open scoped SchwartzMap

namespace ConvolutionDensity


end ConvolutionDensity

open SchwartzMap
open scoped FourierTransform ComplexInnerProductSpace

noncomputable section

namespace ConvolutionDensity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Plancherel isometry: the `L²` Fourier transform on a real
finite-dimensional inner product space `V` is a `ℂ`-linear isometric
equivalence of `L²(V; ℂ)` with itself. This is the operator-theoretic
incarnation of the Plancherel theorem. -/
def fourierL2Equiv : (Lp (α := V) ℂ 2) ≃ₗᵢ[ℂ] (Lp (α := V) ℂ 2) :=
  MeasureTheory.Lp.fourierTransformₗᵢ V ℂ

end ConvolutionDensity
