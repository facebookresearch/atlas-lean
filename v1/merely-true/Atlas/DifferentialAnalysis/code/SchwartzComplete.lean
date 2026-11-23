/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Atlas.DifferentialAnalysis.code.SchwartzSeminormsFix

open scoped SchwartzMap
open Filter Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A sequence of Schwartz functions is Cauchy in the Schwartz topology whenever it is Cauchy
with respect to every individual seminorm `‖·‖_{k,n}`. -/
theorem all_cauchy_implies_cauchySeq
    (u : ℕ → 𝓢(E, F))
    (hcauchy : ∀ (k n : ℕ), ∀ ε > 0, ∃ N, ∀ a b, N ≤ a → N ≤ b →
      SchwartzMap.seminorm ℝ k n (u a - u b) < ε) : CauchySeq u := by
  have hws := schwartz_withSeminorms ℝ E F
  rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff]
  erw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf _).mp hws]
  rw [Filter.tendsto_iInf]
  intro ⟨k, n⟩
  rw [Filter.tendsto_comap_iff, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hcauchy k n ε hε
  refine ⟨(N, N), fun ⟨a, b⟩ ⟨ha, hb⟩ => ?_⟩
  simp only [Function.comp_def, Prod.map_apply, dist_zero_right, Real.norm_eq_abs,
    SchwartzMap.schwartzSeminormFamily_apply]
  rw [abs_of_nonneg (by positivity : 0 ≤ (SchwartzMap.seminorm ℝ k n) (u b - u a)),
    map_sub_rev]
  exact hN a b ha hb

end

noncomputable section

/-- "Diagonal" version of `all_cauchy_implies_cauchySeq`: testing Cauchyness against the
finite-supremum seminorm `sup_{(p, q) ≤ (K, K)} ‖·‖_{p,q}` for every `K` is enough. -/
theorem diag_cauchy_implies_cauchySeq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℕ → 𝓢(E, F))
    (hcauchy : ∀ K : ℕ, ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
      (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (u n - u m) < ε) :
    CauchySeq u := by
  apply all_cauchy_implies_cauchySeq u
  intro k n ε hε
  set K := max k n
  obtain ⟨N, hN⟩ := hcauchy K ε hε
  refine ⟨N, fun a b ha hb => ?_⟩
  calc SchwartzMap.seminorm ℝ k n (u a - u b)
      ≤ (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (u a - u b) :=
        SchwartzSeminorms.individual_le_sup_seminorm (le_max_left k n) (le_max_right k n) _
    _ < ε := hN a b ha hb

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A Cauchy sequence in the Schwartz space is Cauchy with respect to every individual
seminorm `‖·‖_{k,n}`. -/
theorem cauchySeq_seminorm (u : ℕ → 𝓢(E, F)) (hu : CauchySeq u)
    (k n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ m l, N ≤ m → N ≤ l →
      SchwartzMap.seminorm ℝ k n (u m - u l) < ε := by
  rw [cauchySeq_iff_tendsto] at hu
  rw [uniformity_eq_comap_nhds_zero] at hu
  rw [Filter.tendsto_comap_iff] at hu
  have hws := schwartz_withSeminorms ℝ E F
  have hcont := hws.continuous_seminorm (k, n)
  have hball : (SchwartzMap.seminorm ℝ k n).ball 0 ε ∈ 𝓝 (0 : 𝓢(E, F)) :=
    Seminorm.ball_mem_nhds hcont hε
  have hmem := hu hball
  rw [Filter.mem_map, Filter.mem_atTop_sets] at hmem
  obtain ⟨⟨N₁, N₂⟩, hN⟩ := hmem
  refine ⟨max N₁ N₂, fun m l hm hl => ?_⟩
  have h := hN (m, l) ⟨le_trans (le_max_left _ _) hm, le_trans (le_max_right _ _) hl⟩
  simp only [Set.mem_preimage, Function.comp, Prod.map, Seminorm.mem_ball, sub_zero] at h
  rwa [map_sub_rev] at h

end SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The pointwise difference between the `n`-th iterated derivatives of two Schwartz functions
is dominated by the Schwartz seminorm `‖u m - u l‖_{0, n}`. -/
lemma iterFDeriv_sub_le_seminorm (u : ℕ → 𝓢(E, F)) (n m l : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (↑(u m)) x - iteratedFDeriv ℝ n (↑(u l)) x‖ ≤
      SchwartzMap.seminorm ℝ 0 n (u m - u l) := by
  have hsub : iteratedFDeriv ℝ n (↑(u m)) x - iteratedFDeriv ℝ n (↑(u l)) x =
      iteratedFDeriv ℝ n (↑(u m - u l)) x := by
    have hcoerce : (↑(u m - u l) : E → F) = (↑(u m) : E → F) - ↑(u l) := by
      ext y; simp [SchwartzMap.sub_apply]
    conv_lhs => rw [show iteratedFDeriv ℝ n (↑(u m)) x - iteratedFDeriv ℝ n (↑(u l)) x =
      (iteratedFDeriv ℝ n (↑(u m)) - iteratedFDeriv ℝ n (↑(u l))) x from rfl]
    rw [← iteratedFDeriv_sub ((u m).smooth n) ((u l).smooth n), hcoerce]
  rw [hsub]
  have h := SchwartzMap.le_seminorm ℝ 0 n (u m - u l) x
  simpa [pow_zero, one_mul] using h

/-- The pointwise limit `g` of a Cauchy sequence of Schwartz functions is smooth, and its
iterated derivatives are the pointwise limits of the iterated derivatives of the sequence. -/
theorem schwartz_cauchySeq_limit_contDiff [CompleteSpace F]
    (u : ℕ → 𝓢(E, F)) (hu : CauchySeq u) :
    ∃ g : E → F, ContDiff ℝ (⊤ : ℕ∞) g ∧
      (∀ n x, Tendsto (fun m => iteratedFDeriv ℝ n (↑(u m)) x) atTop
        (nhds (iteratedFDeriv ℝ n g x))) := by

  have hptlim : ∀ n : ℕ, ∀ x : E,
      CauchySeq (fun m => iteratedFDeriv ℝ n (↑(u m)) x) := by
    intro n x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := SchwartzMap.cauchySeq_seminorm u hu 0 n ε hε
    exact ⟨N, fun m hm l hl => by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (iterFDeriv_sub_le_seminorm u n m l x) (hN m l hm hl)⟩

  let G : ∀ n : ℕ, E → (E [×n]→L[ℝ] F) := fun n x =>
    limUnder atTop (fun m => iteratedFDeriv ℝ n (↑(u m)) x)
  have hGlim : ∀ n x, Tendsto (fun m => iteratedFDeriv ℝ n (↑(u m)) x) atTop (nhds (G n x)) :=
    fun n x => (hptlim n x).tendsto_limUnder

  have hUnif : ∀ n, TendstoUniformly (fun m x => iteratedFDeriv ℝ n (↑(u m)) x) (G n) atTop := by
    intro n
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := SchwartzMap.cauchySeq_seminorm u hu 0 n (ε/2) (half_pos hε)
    rw [Filter.eventually_atTop]
    refine ⟨N, fun m hm x => ?_⟩
    rw [dist_comm]
    have hle : dist (iteratedFDeriv ℝ n (↑(u m)) x) (G n x) ≤ ε/2 :=
      le_of_tendsto (Tendsto.dist tendsto_const_nhds (hGlim n x))
        (Filter.eventually_atTop.mpr ⟨N, fun l hl => le_of_lt (by
          rw [dist_eq_norm]
          exact lt_of_le_of_lt (iterFDeriv_sub_le_seminorm u n m l x) (hN m l hm hl))⟩)
    linarith

  have hHasFDeriv : ∀ n x, HasFDerivAt (G n)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F) (G (n+1) x)) x := by
    intro n
    have hunif_fderiv : TendstoUniformly
        (fun m x => fderiv ℝ (iteratedFDeriv ℝ n (↑(u m))) x)
        (fun x => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F) (G (n+1) x))
        atTop := by
      convert ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).isometry.uniformContinuous).comp_tendstoUniformly (hUnif (n+1)) using 1
    exact hasFDerivAt_of_tendstoUniformly hunif_fderiv
      (fun m x => ((u m).smooth (n+1)).differentiable_iteratedFDeriv
        (by exact_mod_cast Nat.lt_succ_iff.mpr le_rfl) x |>.hasFDerivAt)
      (fun x => hGlim n x)

  let g : E → F := fun x => (continuousMultilinearCurryFin0 ℝ E F) (G 0 x)
  have hIterEq : ∀ n : ℕ, ∀ x, iteratedFDeriv ℝ n g x = G n x := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp]
      simp [g]
    | succ n ih =>
      intro x
      have h1 := congr_fun (@iteratedFDeriv_succ_eq_comp_left ℝ _ E _ _ F _ _ g n) x
      rw [h1, Function.comp_apply]
      conv_lhs => rw [show iteratedFDeriv ℝ n g = G n from funext ih]
      rw [(hHasFDeriv n x).fderiv]
      simp [LinearIsometryEquiv.symm_apply_apply]

  refine ⟨g, ?_, ?_⟩
  ·
    rw [contDiff_infty]
    intro n
    exact contDiff_of_differentiable_iteratedFDeriv (fun m hm => by
      rw [show iteratedFDeriv ℝ m g = G m from funext (hIterEq m)]
      exact fun x => (hHasFDeriv m x).differentiableAt)
  ·
    intro n x
    rw [hIterEq n x]
    exact hGlim n x


/-- Melrose Proposition 6.7 (Schwartz completeness): the Schwartz space `𝓢(E, F)` is complete
whenever the target `F` is complete. -/
theorem instCompleteSpaceSchwartz [CompleteSpace F] : CompleteSpace 𝓢(E, F) := by
  have hcg : (uniformity (𝓢(E, F))).IsCountablyGenerated := by
    have hws := schwartz_withSeminorms ℝ E F
    haveI := hws.topologicalAddGroup
    have hcg0 : (𝓝 (0 : 𝓢(E, F))).IsCountablyGenerated := by
      erw [(schwartzSeminormFamily ℝ E F).withSeminorms_iff_nhds_eq_iInf.mp hws]
      exact Filter.iInf.isCountablyGenerated _
    exact @IsUniformAddGroup.uniformity_countably_generated _ _ _ _ hcg0
  exact @UniformSpace.complete_of_cauchySeq_tendsto _ _ hcg (fun u hu => by

    obtain ⟨g, hg_smooth, hg_conv⟩ := schwartz_cauchySeq_limit_contDiff u hu

    have hdecay : ∀ k n : ℕ, ∃ C, ∀ x : E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
      intro k n
      obtain ⟨N, hN⟩ := SchwartzMap.cauchySeq_seminorm u hu k n 1 one_pos
      have hne : ((Finset.range (N + 1)).image
          (fun i => SchwartzMap.seminorm ℝ k n (u i))).Nonempty :=
        Finset.Nonempty.image ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N)⟩ _
      set C := ((Finset.range (N + 1)).image
          (fun i => SchwartzMap.seminorm ℝ k n (u i))).max' hne + 1
      have hC : ∀ m : ℕ, SchwartzMap.seminorm ℝ k n (u m) ≤ C := by
        intro m
        by_cases hm : m ≤ N
        · have hmem : SchwartzMap.seminorm ℝ k n (u m) ∈
              (Finset.range (N + 1)).image (fun i => SchwartzMap.seminorm ℝ k n (u i)) :=
            Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hm), rfl⟩
          linarith [Finset.le_max' _ _ hmem]
        · push_neg at hm
          have htri : SchwartzMap.seminorm ℝ k n (u m) ≤
              SchwartzMap.seminorm ℝ k n (u m - u N) + SchwartzMap.seminorm ℝ k n (u N) := by
            have h := map_add_le_add (SchwartzMap.seminorm ℝ k n) (u m - u N) (u N)
            simp only [sub_add_cancel] at h; exact h
          have hNmem : SchwartzMap.seminorm ℝ k n (u N) ∈
              (Finset.range (N + 1)).image (fun i => SchwartzMap.seminorm ℝ k n (u i)) :=
            Finset.mem_image.mpr ⟨N, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl), rfl⟩
          linarith [hN m N (le_of_lt hm) le_rfl, Finset.le_max' _ _ hNmem]
      refine ⟨C, fun x => ?_⟩
      have htend : Tendsto (fun m => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (↑(u m)) x‖) atTop
          (nhds (‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖)) :=
        tendsto_const_nhds.mul ((continuous_norm.tendsto _).comp (hg_conv n x))
      exact le_of_tendsto htend (Filter.Eventually.of_forall (fun m =>
        (SchwartzMap.le_seminorm ℝ k n (u m) x).trans (hC m)))

    let v : 𝓢(E, F) := ⟨g, hg_smooth, hdecay⟩

    have hws := schwartz_withSeminorms ℝ E F
    refine ⟨v, (hws.tendsto_nhds u v).mpr (fun ⟨k, n⟩ ε hε => ?_)⟩
    simp only [SchwartzMap.schwartzSeminormFamily_apply, Filter.eventually_atTop]
    obtain ⟨N, hN⟩ := SchwartzMap.cauchySeq_seminorm u hu k n (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm => ?_⟩
    suffices h : SchwartzMap.seminorm ℝ k n (u m - v) ≤ ε / 2 from
      lt_of_le_of_lt h (half_lt_self hε)
    apply SchwartzMap.seminorm_le_bound ℝ k n (u m - v) (le_of_lt (half_pos hε))
    intro x
    have hcoerce : iteratedFDeriv ℝ n (↑(u m - v)) x =
        iteratedFDeriv ℝ n (↑(u m)) x - iteratedFDeriv ℝ n (↑v) x := by
      have h : (↑(u m - v) : E → F) = (↑(u m) : E → F) - ↑v := by
        ext y; simp [SchwartzMap.sub_apply]
      rw [h, iteratedFDeriv_sub ((u m).smooth n) (v.smooth n)]; rfl
    rw [hcoerce]
    have htend : Tendsto (fun l => ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (↑(u m)) x - iteratedFDeriv ℝ n (↑(u l)) x‖) atTop
        (nhds (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (↑(u m)) x - iteratedFDeriv ℝ n (↑v) x‖)) := by
      apply Tendsto.const_mul
      exact (continuous_norm.tendsto _).comp (tendsto_const_nhds.sub (hg_conv n x))
    apply le_of_tendsto htend
    rw [Filter.eventually_atTop]
    refine ⟨N, fun l hl => ?_⟩
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (↑(u m)) x - iteratedFDeriv ℝ n (↑(u l)) x‖
        ≤ SchwartzMap.seminorm ℝ k n (u m - u l) := by
          have hsub : iteratedFDeriv ℝ n (↑(u m)) x - iteratedFDeriv ℝ n (↑(u l)) x =
              iteratedFDeriv ℝ n (↑(u m - u l)) x := by
            have h : (↑(u m - u l) : E → F) = (↑(u m) : E → F) - ↑(u l) := by
              ext y; simp [SchwartzMap.sub_apply]
            rw [show iteratedFDeriv ℝ n (↑(u m)) x - iteratedFDeriv ℝ n (↑(u l)) x =
              (iteratedFDeriv ℝ n (↑(u m)) - iteratedFDeriv ℝ n (↑(u l))) x from rfl,
              ← iteratedFDeriv_sub ((u m).smooth n) ((u l).smooth n), h]
          rw [hsub]
          exact SchwartzMap.le_seminorm ℝ k n (u m - u l) x
      _ ≤ ε / 2 := le_of_lt (hN m l hm hl))

end
