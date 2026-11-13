/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.Support
import Atlas.DifferentialAnalysis.code.DifferentialOperators
import Atlas.DifferentialAnalysis.code.TemperedDistributions
import Atlas.DifferentialAnalysis.code.SchwartzPartition
import Atlas.DifferentialAnalysis.code.SmoothingOperators

open scoped SchwartzMap LineDeriv Pointwise Manifold
open Distribution

noncomputable section

namespace DifferentialOperators

variable {n : ℕ}


/-- Schwartz decay of the translated–reflected function `y ↦ φ(x − y)`: for every multi-index orders `k, l`, the weighted derivative norm is uniformly bounded in `y`. -/
theorem schwartzTranslateReflect_decay
    {n : ℕ}
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (x : EuclideanSpace ℝ (Fin n)) :
    ∀ k l : ℕ, ∃ C : ℝ, ∀ y : EuclideanSpace ℝ (Fin n),
      ‖y‖ ^ k * ‖iteratedFDeriv ℝ l (fun z => φ (x - z)) y‖ ≤ C := by
  intro k l


  let f : EuclideanSpace ℝ (Fin n) → ℂ := φ
  have hfg : (fun z => φ (x - z)) =
      (fun w => f (x + w)) ∘ (LinearIsometryEquiv.neg ℝ) := by
    ext z
    simp only [Function.comp, LinearIsometryEquiv.coe_neg, sub_eq_add_neg, f]

  have hnorm_eq : ∀ y, ‖iteratedFDeriv ℝ l (fun z => φ (x - z)) y‖ =
      ‖iteratedFDeriv ℝ l f (x - y)‖ := by
    intro y
    rw [hfg]
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]
    rw [iteratedFDeriv_comp_add_left]
    simp only [LinearIsometryEquiv.coe_neg, ← sub_eq_add_neg]


  simp_rw [hnorm_eq]

  set S₀ := SchwartzMap.seminorm ℝ 0 l φ with hS₀_def
  set Sₖ := SchwartzMap.seminorm ℝ k l φ with hSₖ_def
  refine ⟨2 ^ (k - 1) * (‖x‖ ^ k * S₀ + Sₖ), fun y => ?_⟩
  have hx_nn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  have hxy_nn : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
  have hS₀_nn : (0 : ℝ) ≤ S₀ := apply_nonneg _ _
  have hSₖ_nn : (0 : ℝ) ≤ Sₖ := apply_nonneg _ _

  have htri : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    calc ‖y‖ = ‖x - (x - y)‖ := by congr 1; abel
         _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _

  have hpow : ‖y‖ ^ k ≤ (‖x‖ + ‖x - y‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) htri k

  have hbin : (‖x‖ + ‖x - y‖) ^ k ≤ 2 ^ (k - 1) * (‖x‖ ^ k + ‖x - y‖ ^ k) :=
    add_pow_le hx_nn hxy_nn k

  have hderiv_bound : ‖iteratedFDeriv ℝ l f (x - y)‖ ≤ S₀ := by
    have := SchwartzMap.le_seminorm ℝ 0 l φ (x - y)
    rwa [pow_zero, one_mul] at this

  have hxy_decay : ‖x - y‖ ^ k * ‖iteratedFDeriv ℝ l f (x - y)‖ ≤ Sₖ :=
    SchwartzMap.le_seminorm ℝ k l φ (x - y)
  have hderiv_nn : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ l f (x - y)‖ := norm_nonneg _
  calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ l f (x - y)‖
      ≤ (‖x‖ + ‖x - y‖) ^ k * ‖iteratedFDeriv ℝ l f (x - y)‖ :=
        mul_le_mul_of_nonneg_right hpow hderiv_nn
    _ ≤ 2 ^ (k - 1) * (‖x‖ ^ k + ‖x - y‖ ^ k) * ‖iteratedFDeriv ℝ l f (x - y)‖ :=
        mul_le_mul_of_nonneg_right hbin hderiv_nn
    _ = 2 ^ (k - 1) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ l f (x - y)‖ +
        ‖x - y‖ ^ k * ‖iteratedFDeriv ℝ l f (x - y)‖) := by ring
    _ ≤ 2 ^ (k - 1) * (‖x‖ ^ k * S₀ + Sₖ) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        exact add_le_add
          (mul_le_mul_of_nonneg_left hderiv_bound (pow_nonneg hx_nn _))
          hxy_decay

/-- The Schwartz function `y ↦ φ(x − y)` obtained by translating and reflecting a Schwartz function `φ` by `x`. -/
def schwartzTranslateReflect
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (x : EuclideanSpace ℝ (Fin n)) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) where
  toFun := fun y => φ (x - y)
  smooth' := φ.smooth'.comp (contDiff_const.sub contDiff_id)
  decay' := schwartzTranslateReflect_decay φ x

/-- Convolution of a tempered distribution `u` with a Schwartz function `φ`: pointwise `(u ∗ φ)(x) = ⟨u, φ(x − ·)⟩`. -/
def temperedConvolution
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => u (schwartzTranslateReflect φ x)




set_option maxHeartbeats 800000 in
/-- The convolution `u ∗ φ` has polynomial growth: there exist `C > 0` and `k : ℕ` with `‖(u ∗ φ)(x)‖ ≤ C · ⟨x⟩^k`. -/
theorem hormander_convolution_polynomial_growth
    {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ x : EuclideanSpace ℝ (Fin n),
        ‖temperedConvolution u φ x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) := by


  obtain ⟨s, C₀, hle⟩ := TemperedDistributions.seminorm_bound_of_continuous u

  have hu_bound : ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ‖u ψ‖ ≤ C₀ * (s.sup (schwartzSeminormFamily ℂ
        (EuclideanSpace ℝ (Fin n)) ℂ)) ψ := by
    intro ψ
    have := Seminorm.le_def.mp hle ψ
    simp only [Seminorm.comp_apply, Seminorm.smul_apply,
      NNReal.smul_def, smul_eq_mul] at this
    exact this


  set K := s.sup (fun p => p.1) with hK_def


  let B := s.sum (fun p => 2 ^ K * (SchwartzMap.seminorm ℝ 0 p.2 φ +
    SchwartzMap.seminorm ℝ p.1 p.2 φ))
  have hB_nn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => by positivity)

  have hB_mem : ∀ p ∈ s, 2 ^ K * (SchwartzMap.seminorm ℝ 0 p.2 φ +
      SchwartzMap.seminorm ℝ p.1 p.2 φ) ≤ B := by
    intro p hp
    apply Finset.single_le_sum _ hp
    intro q _
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))


  refine ⟨↑C₀ * B + 1, 2 * K, by positivity, fun x => ?_⟩
  have hx2_pos : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have hx2_ge1 : (1 : ℝ) ≤ (1 + ‖x‖ ^ 2) ^ K :=
    one_le_pow₀ (show (1 : ℝ) ≤ 1 + ‖x‖ ^ 2 by nlinarith [sq_nonneg ‖x‖])


  have hrpow_eq : (1 + ‖x‖ ^ 2) ^ ((↑(2 * K) : ℝ) / 2) = (1 + ‖x‖ ^ 2) ^ K := by
    have : ((↑(2 * K) : ℝ)) / 2 = (K : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
  rw [hrpow_eq]

  show ‖u (schwartzTranslateReflect φ x)‖ ≤ (↑C₀ * B + 1) * (1 + ‖x‖ ^ 2) ^ K

  calc ‖u (schwartzTranslateReflect φ x)‖
      ≤ ↑C₀ * (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n)) ℂ))
          (schwartzTranslateReflect φ x) := hu_bound _
    _ ≤ ↑C₀ * (B * (1 + ‖x‖ ^ 2) ^ K) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ ↑C₀)

        apply Seminorm.finset_sup_apply_le (by positivity)
        intro ⟨k, l⟩ hkl
        rw [SchwartzMap.schwartzSeminormFamily_apply]

        apply le_trans (SchwartzMap.seminorm_le_bound ℂ k l
          (schwartzTranslateReflect φ x)
          (by positivity : 0 ≤ 2 ^ (k - 1) * (‖x‖ ^ k *
            SchwartzMap.seminorm ℝ 0 l φ + SchwartzMap.seminorm ℝ k l φ))
          (fun y => ?_))
        ·
          calc 2 ^ (k - 1) * (‖x‖ ^ k * SchwartzMap.seminorm ℝ 0 l φ +
                SchwartzMap.seminorm ℝ k l φ)
              ≤ 2 ^ K * (‖x‖ ^ k * SchwartzMap.seminorm ℝ 0 l φ +
                SchwartzMap.seminorm ℝ k l φ) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le k 1 |>.trans
                  (Finset.le_sup (f := fun p => p.1) hkl))
            _ ≤ 2 ^ K * ((1 + ‖x‖ ^ 2) ^ K * SchwartzMap.seminorm ℝ 0 l φ +
                (1 + ‖x‖ ^ 2) ^ K * SchwartzMap.seminorm ℝ k l φ) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply add_le_add
                · apply mul_le_mul_of_nonneg_right _ (by positivity)
                  calc ‖x‖ ^ k ≤ (1 + ‖x‖ ^ 2) ^ k :=
                        pow_le_pow_left₀ (norm_nonneg _)
                          (by nlinarith [sq_nonneg (‖x‖ - 1)]) k
                    _ ≤ (1 + ‖x‖ ^ 2) ^ K :=
                        pow_le_pow_right₀ (by nlinarith [sq_nonneg ‖x‖])
                          (Finset.le_sup (f := fun p => p.1) hkl)
                · exact le_mul_of_one_le_left (by positivity) hx2_ge1
            _ = 2 ^ K * (SchwartzMap.seminorm ℝ 0 l φ + SchwartzMap.seminorm ℝ k l φ) *
                (1 + ‖x‖ ^ 2) ^ K := by ring
            _ ≤ B * (1 + ‖x‖ ^ 2) ^ K := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact hB_mem ⟨k, l⟩ hkl
        ·


          have hnorm_eq : ∀ z, ‖iteratedFDeriv ℝ l (⇑(schwartzTranslateReflect φ x)) z‖ =
              ‖iteratedFDeriv ℝ l (↑φ) (x - z)‖ := by
            intro z
            show ‖iteratedFDeriv ℝ l (fun z => φ (x - z)) z‖ =
              ‖iteratedFDeriv ℝ l (↑φ) (x - z)‖
            have hfg : (fun z => φ (x - z)) =
                (fun w => (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) (x + w)) ∘
                  (LinearIsometryEquiv.neg ℝ) := by
              ext z; simp [Function.comp, sub_eq_add_neg]
            rw [hfg, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right,
              iteratedFDeriv_comp_add_left]
            simp [sub_eq_add_neg]
          simp_rw [hnorm_eq]
          have hS₀ := SchwartzMap.le_seminorm ℝ 0 l φ (x - y)
          rw [pow_zero, one_mul] at hS₀
          have hSk := SchwartzMap.le_seminorm ℝ k l φ (x - y)
          have htri : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
            calc ‖y‖ = ‖x - (x - y)‖ := by congr 1; abel
                 _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
          have hpow : ‖y‖ ^ k ≤ (‖x‖ + ‖x - y‖) ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) htri k
          have hbin : (‖x‖ + ‖x - y‖) ^ k ≤
              2 ^ (k - 1) * (‖x‖ ^ k + ‖x - y‖ ^ k) :=
            add_pow_le (norm_nonneg _) (norm_nonneg _) k
          calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ l (↑φ) (x - y)‖
              ≤ (‖x‖ + ‖x - y‖) ^ k * ‖iteratedFDeriv ℝ l (↑φ) (x - y)‖ :=
                mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
            _ ≤ 2 ^ (k - 1) * (‖x‖ ^ k + ‖x - y‖ ^ k) *
                  ‖iteratedFDeriv ℝ l (↑φ) (x - y)‖ :=
                mul_le_mul_of_nonneg_right hbin (norm_nonneg _)
            _ = 2 ^ (k - 1) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ l (↑φ) (x - y)‖ +
                  ‖x - y‖ ^ k * ‖iteratedFDeriv ℝ l (↑φ) (x - y)‖) := by ring
            _ ≤ 2 ^ (k - 1) * (‖x‖ ^ k * SchwartzMap.seminorm ℝ 0 l φ +
                  SchwartzMap.seminorm ℝ k l φ) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hS₀ (by positivity))
                  hSk
    _ = ↑C₀ * B * (1 + ‖x‖ ^ 2) ^ K := by ring
    _ ≤ (↑C₀ * B + 1) * (1 + ‖x‖ ^ 2) ^ K := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith






/-- A tempered distribution `u` vanishes on a compactly supported Schwartz test function whose support is disjoint from the distributional support of `u`. -/
theorem tempered_vanishing_outside_dsupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (u : 𝓢'(E, F))
    (ψ : 𝓢(E, ℂ))
    (hψ : HasCompactSupport ψ)
    (hψ_disj : Disjoint (tsupport (⇑ψ)) (dsupport u)) :
    u ψ = 0 := by
  classical
  have hts_closed : IsClosed (tsupport (⇑ψ)) := isClosed_tsupport _
  have h_van_data : ∀ y, y ∉ dsupport (⇑u) →
      ∃ s : Set E, IsVanishingOn (⇑u) s ∧ IsOpen s ∧ y ∈ s := by
    intro y hy; rwa [notMem_dsupport_iff] at hy
  let S : E → Set E := fun y =>
    if hy : y ∈ dsupport (⇑u) then (tsupport (⇑ψ))ᶜ
    else (h_van_data y hy).choose
  have hS_open : ∀ y, IsOpen (S y) := by
    intro y; simp only [S]
    split_ifs with hy
    · exact hts_closed.isOpen_compl
    · exact (h_van_data y hy).choose_spec.2.1
  have hS_mem : ∀ y, y ∈ S y := by
    intro y; simp only [S]
    split_ifs with hy
    · exact Set.mem_compl (fun h => hψ_disj.ne_of_mem h hy rfl)
    · exact (h_van_data y hy).choose_spec.2.2
  have hcov : Set.univ ⊆ ⋃ y, S y :=
    fun y _ => Set.mem_iUnion.mpr ⟨y, hS_mem y⟩
  obtain ⟨ρ, hρ_sub⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, E) isClosed_univ S hS_open hcov
  have hlf := ρ.locallyFinite
  have hfin : {i | (Function.support (⇑(ρ i)) ∩ tsupport (⇑ψ)).Nonempty}.Finite :=
    hlf.finite_nonempty_inter_compact hψ
  set s := hfin.toFinset with hs_def
  have hρ_smooth : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (ρ i : E → ℝ) := by
    intro i; rw [← contMDiff_iff_contDiff]; exact (ρ i).contMDiff
  have hprod_cs : ∀ i, HasCompactSupport (fun x => (↑(ρ i x) : ℂ) * ψ x) :=
    fun i => hψ.mul_left
  have hprod_smooth : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (↑(ρ i x) : ℂ) * ψ x) :=
    fun i => (Complex.ofRealCLM.contDiff.comp (hρ_smooth i)).mul (ψ.smooth ⊤)
  let g : E → 𝓢(E, ℂ) := fun i => (hprod_cs i).toSchwartzMap (hprod_smooth i)
  have hg_vanish : ∀ i, u (g i) = 0 := by
    intro i
    by_cases hi : i ∈ dsupport (⇑u)
    · have hSi : S i = (tsupport (⇑ψ))ᶜ := by simp [S, hi]
      have hρi_sub : tsupport (ρ i : E → ℝ) ⊆ (tsupport (⇑ψ))ᶜ := hSi ▸ hρ_sub i
      have heq : g i = 0 := by
        ext y
        have hval := (hprod_cs i).toSchwartzMap_toFun (hprod_smooth i) y
        simp only [g] at hval ⊢
        rw [hval]
        simp only [SchwartzMap.coe_zero, Pi.zero_apply]
        by_cases hψy : ψ y = 0
        · simp [hψy]
        · have hy_ts : y ∈ tsupport (⇑ψ) := subset_tsupport _ (Function.mem_support.mpr hψy)
          have hy_not_ts_ρ : y ∉ tsupport (ρ i : E → ℝ) := fun h => (hρi_sub h) hy_ts
          have hρiy : (ρ i : E → ℝ) y = 0 := by
            by_contra h
            exact hy_not_ts_ρ (subset_tsupport _ (Function.mem_support.mpr h))
          simp [hρiy]
      rw [heq, map_zero]
    · have hSi : S i = (h_van_data i hi).choose := by simp [S, hi]
      have hvan : IsVanishingOn (⇑u) (S i) := hSi ▸ (h_van_data i hi).choose_spec.1
      apply hvan
      have heq : ∀ x, (g i) x = (↑(ρ i x) : ℂ) * ψ x :=
        (hprod_cs i).toSchwartzMap_toFun (hprod_smooth i)
      calc tsupport ⇑(g i) ⊆ tsupport (ρ i : E → ℝ) := by
              apply closure_mono
              intro x hx
              rw [Function.mem_support] at hx ⊢
              intro hρx; apply hx; simp [heq, hρx]
           _ ⊆ S i := hρ_sub i
  have hψ_eq : ψ = ∑ i ∈ s, g i := by
    ext x
    have hsum_app : (∑ i ∈ s, g i) x = ∑ i ∈ s, (g i) x := by
      change (⇑(∑ i ∈ s, g i)) x = _; simp
    rw [hsum_app]
    have heq : ∀ i, (g i) x = (↑(ρ i x) : ℂ) * ψ x :=
      fun i => (hprod_cs i).toSchwartzMap_toFun (hprod_smooth i) x
    simp_rw [heq, ← Finset.sum_mul]
    by_cases hψx : ψ x = 0
    · simp [hψx]
    · have hx_supp : x ∈ tsupport (⇑ψ) := subset_tsupport _ (Function.mem_support.mpr hψx)
      have hρ_zero : ∀ i, i ∉ s → (ρ i) x = 0 := by
        intro i hi; by_contra h
        exact hi (hs_def ▸ hfin.mem_toFinset.mpr ⟨x, Function.mem_support.mpr h, hx_supp⟩)
      have hsum_one : ∑ᶠ i, (ρ i) x = 1 := ρ.sum_eq_one (Set.mem_univ x)
      have hsupp : Function.support (fun i => (ρ i) x) ⊆ ↑s := by
        intro i hi; rw [Finset.mem_coe]; by_contra hi'
        exact (Function.mem_support.mp hi) (hρ_zero i hi')
      rw [finsum_eq_sum_of_support_subset _ hsupp] at hsum_one
      have hcsum : (∑ i ∈ s, (↑(ρ i x) : ℂ)) = 1 := by
        rw [← Complex.ofReal_one, ← hsum_one]; simp
      rw [hcsum, one_mul]
  rw [hψ_eq, map_sum]
  exact Finset.sum_eq_zero (fun i _ => hg_vanish i)

/-- Support of `u ∗ φ` (when `φ` has compact support) is contained in `dsupport u + tsupport φ`. -/
theorem hormander_convolution_support
    {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (hφ : HasCompactSupport φ) :
    Function.support (temperedConvolution u φ) ⊆
      dsupport u + tsupport (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) := by


  intro x hx
  by_contra hx_not_mem

  rw [Function.mem_support] at hx


  apply hx

  set ψ := schwartzTranslateReflect φ x with hψ_def
  show u ψ = 0

  have hψ_cs : HasCompactSupport ψ := by

    change IsCompact (tsupport (⇑ψ))
    have heq : (⇑ψ : EuclideanSpace ℝ (Fin n) → ℂ) =
        ⇑φ ∘ Homeomorph.subLeft x := by
      ext y; rfl
    rw [heq]
    exact hφ.comp_homeomorph _

  have hψ_disj : Disjoint (tsupport (⇑ψ)) (dsupport u) := by
    rw [Set.disjoint_iff]
    intro y hy
    obtain ⟨hy_ts, hy_ds⟩ := hy
    have heq : (⇑ψ : EuclideanSpace ℝ (Fin n) → ℂ) =
        ⇑φ ∘ Homeomorph.subLeft x := by ext z; rfl
    rw [heq, tsupport_comp_eq_preimage] at hy_ts

    have hxy : x - y ∈ tsupport (⇑φ) := hy_ts
    apply hx_not_mem
    have : x = y + (x - y) := by abel
    rw [this]
    exact Set.add_mem_add hy_ds hxy

  exact tempered_vanishing_outside_dsupport u ψ hψ_cs hψ_disj

end DifferentialOperators
