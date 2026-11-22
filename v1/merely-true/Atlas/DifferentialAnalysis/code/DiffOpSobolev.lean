/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.DifferentialOperators
import Atlas.DifferentialAnalysis.code.SobolevEmbedding
import Atlas.DifferentialAnalysis.code.FourierInversion
import Atlas.DifferentialAnalysis.code.SobolevDerivatives
import Mathlib.Algebra.MvPolynomial.Degrees

open scoped SchwartzMap ContDiff FourierTransform
open DifferentialOperators SobolevEmbedding SobolevSpace MvPolynomial Filter Topology MeasureTheory

noncomputable section

namespace DiffOpSobolev

variable (n : ℕ)

/-- Non-degeneracy of the Schwartz pairing: if a Schwartz function `ψ` pairs to zero
against every Schwartz function via the canonical Schwartz-to-tempered-distribution
embedding, then `ψ = 0`. -/
lemma schwartz_pairing_nondeg
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (h : ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (SchwartzMap.toTemperedDistributionCLM (EuclideanSpace ℝ (Fin n)) ℂ) f ψ = 0) :
    ψ = 0 := by
  set E := EuclideanSpace ℝ (Fin n)
  have hψ_ae : (ψ : E → ℂ) =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero (ψ.integrable.locallyIntegrable)
    intro g hg_smooth hg_supp
    let f_s : 𝓢(E, ℂ) := (hg_supp.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg_smooth)
    specialize h f_s
    simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply] at h
    convert h using 1
    congr 1; ext x
    simp only [f_s, Function.comp, HasCompactSupport.toSchwartzMap_toFun]
    change (g x : ℂ) * ψ x = ψ x * (g x : ℂ)
    ring
  exact SchwartzMap.ext (fun x => congr_fun
    ((Continuous.ae_eq_iff_eq volume ψ.continuous continuous_const).mp hψ_ae) x)

/-- Key inductive step for weak density: if `f₀` already matches the distribution `u`
on a finite set `S'` and any `ψ` annihilated by tests vanishing on `S'` is also
annihilated by `ι g`, then `ι f₀ ψ = u ψ`. -/
lemma hall_implies_eq
    (ι : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hι : ι = SchwartzMap.toTemperedDistributionCLM (EuclideanSpace ℝ (Fin n)) ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (f₀ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (S' : Finset (𝓢(EuclideanSpace ℝ (Fin n), ℂ)))
    (hf₀ : ∀ φ ∈ S', ι f₀ φ = u φ)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (hall : ∀ g, (∀ φ ∈ S', ι g φ = 0) → ι g ψ = 0) :
    ι f₀ ψ = u ψ := by
  induction S' using Finset.cons_induction generalizing ψ with
  | empty =>
    have hψ0 : ψ = 0 := by
      subst hι
      exact schwartz_pairing_nondeg n ψ (fun f => hall f (fun φ h => absurd h (by simp)))
    simp [hψ0]
  | cons φ₀ S'' hφ₀S'' ih =>
    by_cases h_inner : ∀ g, (∀ φ ∈ S'', ι g φ = 0) → ι g ψ = 0
    · exact ih (fun φ hφ => hf₀ φ (Finset.mem_cons.mpr (Or.inr hφ))) ψ h_inner
    · push Not at h_inner
      obtain ⟨g₀, hg₀_zero, hg₀_ne⟩ := h_inner
      have hg₀φ₀ : ι g₀ φ₀ ≠ 0 := by
        intro heq0
        exact hg₀_ne (hall g₀ (fun φ hφ => by
          rw [Finset.mem_cons] at hφ
          rcases hφ with rfl | hφ
          · exact heq0
          · exact hg₀_zero φ hφ))
      set c₀ := ι g₀ ψ / ι g₀ φ₀
      suffices key : ι f₀ (ψ - c₀ • φ₀) = u (ψ - c₀ • φ₀) by
        have h1 : ι f₀ ψ - c₀ * ι f₀ φ₀ = u ψ - c₀ * u φ₀ := by
          simp only [map_sub, map_smul, smul_eq_mul] at key
          exact key
        have h2 : ι f₀ φ₀ = u φ₀ := hf₀ φ₀ (Finset.mem_cons.mpr (Or.inl rfl))
        linear_combination h1 + c₀ * h2
      apply ih (fun φ hφ => hf₀ φ (Finset.mem_cons.mpr (Or.inr hφ)))
      intro g hg
      simp only [map_sub, map_smul, smul_eq_mul]
      set a := ι g φ₀ / ι g₀ φ₀
      have hg' : ∀ φ ∈ Finset.cons φ₀ S'' hφ₀S'', ι (g - a • g₀) φ = 0 := by
        intro φ hφ
        simp only [map_sub, map_smul]
        rw [Finset.mem_cons] at hφ
        rcases hφ with rfl | hφ
        · simp [a, div_mul_cancel₀ _ hg₀φ₀]
        · simp [hg φ hφ, hg₀_zero φ hφ]
      have hval' : ι g ψ - a * ι g₀ ψ = 0 := by
        have hval := hall (g - a • g₀) hg'
        simp only [map_sub, map_smul] at hval
        exact hval
      have h2 : a * ι g₀ ψ = c₀ * ι g φ₀ := by
        simp only [a, c₀]
        field_simp
      linear_combination hval' + h2

/-- Given any tempered distribution `u` and any finite set `S` of test functions,
there exists a Schwartz function `f` whose Schwartz-distribution image agrees with `u`
on every element of `S`. -/
lemma schwartz_joint_eval
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (S : Finset (𝓢(EuclideanSpace ℝ (Fin n), ℂ))) :
    ∃ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ∀ φ ∈ S, (SchwartzMap.toTemperedDistributionCLM
        (EuclideanSpace ℝ (Fin n)) ℂ) f φ = u φ := by
  set ι := SchwartzMap.toTemperedDistributionCLM (EuclideanSpace ℝ (Fin n)) ℂ
  induction S using Finset.cons_induction with
  | empty => exact ⟨0, fun φ h => absurd h (by simp)⟩
  | cons ψ S' hψS' ih =>
    obtain ⟨f₀, hf₀⟩ := ih
    by_cases heq : ι f₀ ψ = u ψ
    · exact ⟨f₀, fun φ hφ => by
        rw [Finset.mem_cons] at hφ
        rcases hφ with rfl | hφ
        · exact heq
        · exact hf₀ φ hφ⟩
    · have hg_exists : ∃ g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
          (∀ φ ∈ S', ι g φ = 0) ∧ ι g ψ ≠ 0 := by
        by_contra hall
        push Not at hall
        exact heq (hall_implies_eq n ι rfl u f₀ S' hf₀ ψ hall)
      obtain ⟨g, hg_zero, hg_ne⟩ := hg_exists
      let c := (u ψ - ι f₀ ψ) / ι g ψ
      have ι_add_smul (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
          (ι (f₀ + c • g)) φ = ι f₀ φ + c * ι g φ := by
        simp [map_add, map_smul, smul_eq_mul]
      refine ⟨f₀ + c • g, fun φ hφ => ?_⟩
      rw [Finset.mem_cons] at hφ
      rcases hφ with rfl | hφ
      · rw [ι_add_smul]
        simp [c, div_mul_cancel₀ _ hg_ne, add_sub_cancel]
      · rw [ι_add_smul, hg_zero φ hφ, mul_zero, add_zero, hf₀ φ hφ]


/-- The canonical embedding of Schwartz functions into tempered distributions has
dense range with respect to the weak (pointwise) topology on distributions. -/
theorem schwartz_weakly_dense :
    DenseRange (SchwartzMap.toTemperedDistributionCLM
      (EuclideanSpace ℝ (Fin n)) ℂ) := by
  set E := EuclideanSpace ℝ (Fin n) with hE
  set ι := SchwartzMap.toTemperedDistributionCLM E ℂ with hι
  intro u
  rw [mem_closure_iff_nhds]
  intro V hV
  choose f_S hf_S using fun S : Finset (𝓢(E, ℂ)) => schwartz_joint_eval n u S
  have htendsto : Tendsto (fun S => ι (f_S S)) atTop (𝓝 u) := by
    rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
    intro φ
    apply tendsto_const_nhds.congr'
    rw [EventuallyEq, Filter.eventually_atTop]
    exact ⟨{φ}, fun S hS => (hf_S S φ (hS (Finset.mem_singleton.mpr rfl))).symm⟩
  have hev : ∀ᶠ S in atTop, ι (f_S S) ∈ V := htendsto hV
  obtain ⟨S₀, hS₀⟩ := hev.exists
  exact ⟨ι (f_S S₀), hS₀, ⟨f_S S₀, rfl⟩⟩

/-- A tempered distribution `u` lies in the Sobolev space `H^m` if it is represented
by integration against an element of `SobolevSpace n m`. -/
def IsInSobolev (m : ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ f : SobolevSpace n m,
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      u φ = ∫ x : EuclideanSpace ℝ (Fin n), φ x • f x




/-- Sum of the components of a multi-index `α` over coordinates `≥ k`. -/
def tailMultiIndexSum {n : ℕ} (α : Fin n → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun j : Fin n => k ≤ j.val), α i

/-- The tail sum from index `0` equals the total sum of the multi-index. -/
lemma tailMultiIndexSum_zero {n : ℕ} (α : Fin n → ℕ) :
    tailMultiIndexSum α 0 = ∑ i, α i := by
  simp [tailMultiIndexSum]

/-- If `k ≥ n`, the tail sum `∑_{i ≥ k} α i` is empty and hence `0`. -/
lemma tailMultiIndexSum_ge {n : ℕ} (α : Fin n → ℕ) (k : ℕ) (hk : n ≤ k) :
    tailMultiIndexSum α k = 0 := by
  simp only [tailMultiIndexSum]
  apply Finset.sum_eq_zero
  intro i hi
  simp [Finset.mem_filter] at hi
  omega

/-- Recurrence for the tail sum: peel off the term at index `k`. -/
lemma tailMultiIndexSum_succ {n : ℕ} (α : Fin n → ℕ) (k : ℕ) (hk : k < n) :
    tailMultiIndexSum α k = α ⟨k, hk⟩ + tailMultiIndexSum α (k + 1) := by
  simp only [tailMultiIndexSum]
  have hsplit : Finset.univ.filter (fun j : Fin n => k ≤ j.val) =
      {⟨k, hk⟩} ∪ Finset.univ.filter (fun j : Fin n => k + 1 ≤ j.val) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton]
    constructor
    · intro hx
      by_cases hxk : x.val = k
      · left; exact Fin.ext hxk
      · right; omega
    · intro hx
      rcases hx with hx | hx
      · subst hx; simp
      · omega
  rw [hsplit, Finset.sum_union]
  · simp
  · rw [Finset.disjoint_singleton_left]
    simp [Finset.mem_filter]

/-- Auxiliary recursion computing the multi-index iterated partial derivative on
`SobolevSpace n m'` by processing coordinates starting at index `k`. -/
def multiIndexDerivGo {n : ℕ} (α : Fin n → ℕ)
    (k : ℕ) (m' : ℕ) (hsum : tailMultiIndexSum α k ≤ m')
    (u : SobolevSpace n m') : SobolevSpace n (m' - tailMultiIndexSum α k) :=
  if hk : k < n then
    have hαk : α ⟨k, hk⟩ ≤ m' := by
      have := tailMultiIndexSum_succ α k hk
      omega
    let v := SobolevSpace.iteratedPartialDeriv ⟨k, hk⟩ (α ⟨k, hk⟩) hαk u
    have hsum' : tailMultiIndexSum α (k + 1) ≤ m' - α ⟨k, hk⟩ := by
      have := tailMultiIndexSum_succ α k hk
      omega
    have heq : m' - α ⟨k, hk⟩ - tailMultiIndexSum α (k + 1) =
        m' - tailMultiIndexSum α k := by
      have := tailMultiIndexSum_succ α k hk
      omega
    heq ▸ multiIndexDerivGo α (k + 1) (m' - α ⟨k, hk⟩) hsum' v
  else
    have heq : tailMultiIndexSum α k = 0 := tailMultiIndexSum_ge α k (by omega)
    heq ▸ u
  termination_by n - k

/-- The monomial `x^α := ∏ x_i^{α_i}` viewed as a multivariate polynomial. -/
def multiIndexMonomial (α : Fin n → ℕ) : MvPolynomial (Fin n) ℂ :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) 1


/-- Iterated distributional derivatives of order `α` map `H^m` to `H^{m - |α|}`. -/
theorem multiIndexDeriv_memHs {m : ℝ}
    (α : Fin n → ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu : MemHs n m u) :
    MemHs n (m - ↑(∑ i, α i)) (iteratedDistribDeriv n α u) :=
  memHs_iteratedDistribDeriv α u hu




section WitnessAeBound

open TestFunctions
open TemperedDistributions (distribDerivCLM)

/-- Almost-everywhere uniqueness of the Sobolev `L^2` witness: two `L^2` functions
that pair identically against all Schwartz functions via the weighted integral are
equal a.e. -/
theorem sobolev_witness_ae_unique {s : ℝ}
    (g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg₁ : MemLp g₁ 2) (hg₂ : MemLp g₂ 2)
    (hint : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g₁ ξ * φ ξ =
      ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g₂ ξ * φ ξ) :
    g₁ =ᵐ[volume] g₂ := by
  have hg₁_li : LocallyIntegrable g₁ volume :=
    hg₁.locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hg₂_li : LocallyIntegrable g₂ volume :=
    hg₂.locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  apply ae_eq_of_integral_contDiff_smul_eq hg₁_li hg₂_li
  intro g_test hg_smooth hg_supp

  have hw_htg : (fun ξ : EuclideanSpace ℝ (Fin n) => sobolevWeight n s ξ).HasTemperateGrowth := by
    show (fun ξ => (japaneseBracket n ξ) ^ s).HasTemperateGrowth
    have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ (s / 2)).HasTemperateGrowth :=
      Function.hasTemperateGrowth_one_add_norm_sq_rpow _ (s / 2)
    suffices h : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ s) =
        (fun ξ => (1 + ‖ξ‖ ^ 2) ^ (s / 2)) by
      rw [h]; exact this
    ext ξ
    simp only [japaneseBracket]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
    congr 1; ring
  have hψ_smooth := hg_smooth.mul hw_htg.1
  have hψ_supp : HasCompactSupport (fun ξ => g_test ξ * sobolevWeight n s ξ) :=
    hg_supp.mul_right
  set φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    (hψ_supp.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hψ_smooth)
  have key := hint φ

  have heq_lhs : (fun x => g_test x • g₁ x) =
      (fun x => (sobolevWeight n s x : ℂ)⁻¹ * g₁ x * φ x) := by
    ext ξ
    simp only [φ, HasCompactSupport.toSchwartzMap_toFun, Function.comp,
      Complex.ofReal_mul, smul_eq_mul, Complex.real_smul]
    have hw_ne : (sobolevWeight n s ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (sobolevWeight_pos n s ξ))
    field_simp
  have heq_rhs : (fun x => g_test x • g₂ x) =
      (fun x => (sobolevWeight n s x : ℂ)⁻¹ * g₂ x * φ x) := by
    ext ξ
    simp only [φ, HasCompactSupport.toSchwartzMap_toFun, Function.comp,
      Complex.ofReal_mul, smul_eq_mul, Complex.real_smul]
    have hw_ne : (sobolevWeight n s ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (sobolevWeight_pos n s ξ))
    field_simp
  calc ∫ x, g_test x • g₁ x
      = ∫ x, (sobolevWeight n s x : ℂ)⁻¹ * g₁ x * φ x := congr_arg _ heq_lhs
    _ = ∫ x, (sobolevWeight n s x : ℂ)⁻¹ * g₂ x * φ x := key
    _ = ∫ x, g_test x • g₂ x := congr_arg _ heq_rhs.symm

set_option maxHeartbeats 800000 in
/-- Distributional derivative in the `j`-th direction maps Sobolev `H^s` witnesses to
`H^{s-1}` witnesses, with the resulting `L^2` representative bounded pointwise by
`(2π) ‖g‖`. -/
theorem memHs_distribDeriv_with_bound {s : ℝ} (j : Fin n)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g : EuclideanSpace ℝ (Fin n) → ℂ) (hg_mem : MemLp g 2)
    (hg_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g ξ * φ ξ) :
    ∃ g_new : EuclideanSpace ℝ (Fin n) → ℂ,
      MemLp g_new 2 ∧
      (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (𝓕 (distribDerivCLM (F := ℂ) (EuclideanSpace.single j (1 : ℝ)) u)) φ =
          ∫ ξ, (sobolevWeight n (s - 1) ξ : ℂ)⁻¹ * g_new ξ * φ ξ) ∧
      (∀ ξ, ‖g_new ξ‖ ≤ (2 * Real.pi) * ‖g ξ‖) := by

  set ej := EuclideanSpace.single j (1 : ℝ)
  set m_fun : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ =>
    (2 * ↑Real.pi * Complex.I) * ↑(@inner ℝ _ _ ξ ej) *
    (↑(japaneseBracket n ξ))⁻¹
  set g_cand := fun ξ => m_fun ξ * g ξ

  have hcand_bound : ∀ ξ, ‖g_cand ξ‖ ≤ (2 * Real.pi) * ‖g ξ‖ := by
    intro ξ
    show ‖m_fun ξ * g ξ‖ ≤ (2 * Real.pi) * ‖g ξ‖
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    show ‖(2 * ↑Real.pi * Complex.I) * ↑(@inner ℝ _ _ ξ ej) *
      (↑(japaneseBracket n ξ))⁻¹‖ ≤ 2 * Real.pi
    have hjb_pos := japaneseBracket_pos n ξ
    have h_inner_le : |@inner ℝ _ _ ξ ej| ≤ japaneseBracket n ξ := by
      have : |@inner ℝ _ _ ξ ej| ≤ ‖ξ‖ := by
        calc |@inner ℝ _ _ ξ ej|
            ≤ ‖ξ‖ * ‖ej‖ := abs_real_inner_le_norm _ _
          _ = ‖ξ‖ := by rw [PiLp.norm_single, norm_one, mul_one]
      calc |@inner ℝ _ _ ξ ej|
          ≤ ‖ξ‖ := this
        _ ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) := by
            rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
            nlinarith [sq_nonneg ‖ξ‖]
        _ = japaneseBracket n ξ := rfl
    have hnorm_2piI : ‖(2 * ↑Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      rw [show (2 : ℂ) * ↑Real.pi * Complex.I = ↑(2 * Real.pi) * Complex.I by push_cast; ring]
      rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
          Real.norm_of_nonneg (by positivity)]
    rw [norm_mul, norm_mul, hnorm_2piI,
        Complex.norm_real, Real.norm_eq_abs,
        norm_inv, Complex.norm_real, Real.norm_of_nonneg hjb_pos.le]
    calc (2 * Real.pi) * |@inner ℝ _ _ ξ ej| * (japaneseBracket n ξ)⁻¹
        ≤ (2 * Real.pi) * japaneseBracket n ξ * (japaneseBracket n ξ)⁻¹ := by gcongr
      _ = 2 * Real.pi := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hjb_pos)]; ring

  have hcand_mem : MemLp g_cand 2 := by
    have hle : ∀ ξ : EuclideanSpace ℝ (Fin n),
        ‖g_cand ξ‖ ≤ (2 * Real.pi) * ‖g ξ‖ := hcand_bound
    have hm_cont : Continuous m_fun := by
      show Continuous (fun ξ => (2 * ↑Real.pi * Complex.I) * ↑(@inner ℝ _ _ ξ ej) *
        (↑(japaneseBracket n ξ))⁻¹)
      refine Continuous.mul (Continuous.mul continuous_const ?_) ?_
      · exact Complex.continuous_ofReal.comp (Continuous.inner continuous_id continuous_const)
      · refine Continuous.inv₀ (Complex.continuous_ofReal.comp ?_) ?_
        · show Continuous (japaneseBracket n)
          unfold japaneseBracket; fun_prop
        · intro ξ; exact Complex.ofReal_ne_zero.mpr (japaneseBracket_ne_zero n ξ)
    exact hg_mem.of_le_mul
      (hm_cont.aestronglyMeasurable.mul hg_mem.1)
      (Filter.Eventually.of_forall hle)

  have hcand_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 (distribDerivCLM (F := ℂ) ej u)) φ =
        ∫ ξ, (sobolevWeight n (s - 1) ξ : ℂ)⁻¹ * g_cand ξ * φ ξ := by
    intro φ
    have heval : (𝓕 (distribDerivCLM (F := ℂ) ej u)) φ =
        (2 * ↑Real.pi * Complex.I) *
        ((𝓕 u) (SchwartzMap.smulLeftCLM ℂ (fun ξ => (↑(@inner ℝ _ _ ξ ej) : ℂ)) φ)) := by
      change (𝓕 (LineDeriv.lineDerivOpCLM ℂ _ ej u)) φ = _
      rw [show (LineDeriv.lineDerivOpCLM ℂ (𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) ej u) =
        LineDeriv.lineDerivOp ej u from rfl]
      have := TemperedDistribution.fourier_lineDerivOp_eq u ej
      rw [this]; rfl
    rw [heval, hg_eq]
    simp_rw [← smul_eq_mul (a := (2 * ↑Real.pi * Complex.I)), ← integral_smul]
    congr 1; ext ξ; simp only [smul_eq_mul]
    have htemp : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) =>
        (↑(@inner ℝ _ _ ξ ej) : ℂ)) :=
      (Complex.ofRealCLM.comp ((innerSL ℝ).flip ej)).hasTemperateGrowth
    rw [SchwartzMap.smulLeftCLM_apply_apply htemp]; simp only [smul_eq_mul]
    have hjb_pos := japaneseBracket_pos n ξ
    have hjb_ne : (japaneseBracket n ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hjb_pos)
    simp only [sobolevWeight]
    have hws : ((japaneseBracket n ξ ^ (s - 1) : ℝ) : ℂ)⁻¹ *
        ((japaneseBracket n ξ : ℝ) : ℂ)⁻¹ =
        ((japaneseBracket n ξ ^ s : ℝ) : ℂ)⁻¹ := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
          ← Complex.ofReal_inv]
      congr 1
      rw [← Real.rpow_neg hjb_pos.le, ← Real.rpow_neg hjb_pos.le,
          show (japaneseBracket n ξ)⁻¹ = japaneseBracket n ξ ^ ((-1 : ℝ)) from
            (Real.rpow_neg_one (japaneseBracket n ξ)).symm,
          ← Real.rpow_add hjb_pos]
      congr 1; linarith
    rw [← hws]; ring
  exact ⟨g_cand, hcand_mem, hcand_eq, hcand_bound⟩

set_option maxHeartbeats 1600000 in
/-- Iterated `k`-fold partial derivative in the `j`-th direction maps Sobolev `H^s`
witnesses to `H^{s-k}` witnesses with `L^2` representative bounded by `(2π)^k ‖g‖`. -/
theorem memHs_iteratedPartialDeriv_with_bound {s : ℝ} (j : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g : EuclideanSpace ℝ (Fin n) → ℂ) (hg_mem : MemLp g 2)
    (hg_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g ξ * φ ξ) :
    ∃ g_new : EuclideanSpace ℝ (Fin n) → ℂ,
      MemLp g_new 2 ∧
      (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (𝓕 (iteratedPartialDerivDistrib n j k u)) φ =
          ∫ ξ, (sobolevWeight n (s - ↑k) ξ : ℂ)⁻¹ * g_new ξ * φ ξ) ∧
      (∀ ξ, ‖g_new ξ‖ ≤ (2 * Real.pi) ^ k * ‖g ξ‖) := by
  induction k generalizing s u g with
  | zero =>
    refine ⟨g, hg_mem, ?_, ?_⟩
    · simp only [iteratedPartialDerivDistrib, Function.iterate_zero, id_eq,
        Nat.cast_zero, sub_zero]
      exact hg_eq
    · intro ξ; simp only [pow_zero, one_mul]; exact le_refl _
  | succ k ih =>

    obtain ⟨g_k, hg_k_mem, hg_k_eq, hg_k_bound⟩ := @ih s u g hg_mem hg_eq

    have hstep := memHs_distribDeriv_with_bound n j
      (iteratedPartialDerivDistrib n j k u) g_k hg_k_mem hg_k_eq
    obtain ⟨g_new, hg_new_mem, hg_new_eq, hg_new_bound⟩ := hstep
    refine ⟨g_new, hg_new_mem, ?_, ?_⟩
    ·
      intro φ
      simp only [iteratedPartialDerivDistrib, Function.iterate_succ', Function.comp]
      have h := hg_new_eq φ
      convert h using 2
      push_cast; ring
    ·
      intro ξ
      calc ‖g_new ξ‖ ≤ (2 * Real.pi) * ‖g_k ξ‖ := hg_new_bound ξ
        _ ≤ (2 * Real.pi) * ((2 * Real.pi) ^ k * ‖g ξ‖) :=
          mul_le_mul_of_nonneg_left (hg_k_bound ξ) (by positivity)
        _ = (2 * Real.pi) ^ (k + 1) * ‖g ξ‖ := by ring

set_option maxHeartbeats 1600000 in
/-- Sequentially applying the iterated partial derivatives `D_i^{α_i}` along a list
`l` of coordinates preserves the Sobolev structure with an `L^2` witness bounded by
`(2π)^{Σ α} ‖g‖`. -/
theorem memHs_foldr_with_bound {s : ℝ}
    (l : List (Fin n)) (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g : EuclideanSpace ℝ (Fin n) → ℂ) (hg_mem : MemLp g 2)
    (hg_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g ξ * φ ξ) :
    ∃ g_new : EuclideanSpace ℝ (Fin n) → ℂ,
      MemLp g_new 2 ∧
      (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (𝓕 (l.foldr (fun i acc => iteratedPartialDerivDistrib n i (α i) acc) u)) φ =
          ∫ ξ, (sobolevWeight n (s - ↑(l.map (fun j => α j)).sum) ξ : ℂ)⁻¹ * g_new ξ * φ ξ) ∧
      (∀ ξ, ‖g_new ξ‖ ≤ (2 * Real.pi) ^ (l.map (fun j => α j)).sum * ‖g ξ‖) := by
  induction l generalizing s u g with
  | nil =>
    refine ⟨g, hg_mem, ?_, ?_⟩
    · simp only [List.foldr_nil, List.map_nil, List.sum_nil, Nat.cast_zero, sub_zero]
      exact hg_eq
    · intro ξ; simp only [List.map_nil, List.sum_nil, pow_zero, one_mul]; exact le_refl _
  | cons j l ih =>

    obtain ⟨g_tail, hg_tail_mem, hg_tail_eq, hg_tail_bound⟩ := @ih s u g hg_mem hg_eq

    have hstep := memHs_iteratedPartialDeriv_with_bound n j (α j)
      (l.foldr (fun i acc => iteratedPartialDerivDistrib n i (α i) acc) u)
      g_tail hg_tail_mem hg_tail_eq
    obtain ⟨g_new, hg_new_mem, hg_new_eq, hg_new_bound⟩ := hstep
    refine ⟨g_new, hg_new_mem, ?_, ?_⟩
    ·
      intro φ
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      have h := hg_new_eq φ
      convert h using 2
      push_cast; ring
    ·
      intro ξ
      simp only [List.map_cons, List.sum_cons]
      calc ‖g_new ξ‖
          ≤ (2 * Real.pi) ^ (α j) * ‖g_tail ξ‖ := hg_new_bound ξ
        _ ≤ (2 * Real.pi) ^ (α j) * ((2 * Real.pi) ^ (l.map (fun j => α j)).sum * ‖g ξ‖) :=
          mul_le_mul_of_nonneg_left (hg_tail_bound ξ) (by positivity)
        _ = (2 * Real.pi) ^ (α j + (l.map (fun j => α j)).sum) * ‖g ξ‖ := by
          rw [pow_add]; ring

set_option maxHeartbeats 1600000 in
/-- Almost-everywhere pointwise bound: any `L^2` witness `g'` for the iterated
distributional derivative `D^α u` satisfies `‖g' ξ‖ ≤ (2π)^{|α|} ‖g ξ‖` for the
witness `g` of `u`. -/
theorem iteratedDistribDeriv_witness_ae_bound {m : ℝ}
    (α : Fin n → ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g : EuclideanSpace ℝ (Fin n) → ℂ) (hg : MemLp g 2)
    (hug : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u) φ = ∫ ξ, (sobolevWeight n m ξ : ℂ)⁻¹ * g ξ * φ ξ)
    {g' : EuclideanSpace ℝ (Fin n) → ℂ} (hg'_mem : MemLp g' 2)
    (hg'_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 (iteratedDistribDeriv n α u)) φ =
        ∫ ξ, (sobolevWeight n (m - ↑(∑ i, α i)) ξ : ℂ)⁻¹ * g' ξ * φ ξ) :
    ∀ᵐ ξ ∂volume, ‖g' ξ‖ ≤ (2 * Real.pi) ^ (∑ i, α i) * ‖g ξ‖ := by

  have hfoldr := memHs_foldr_with_bound n (List.finRange n) α u g hg hug
  obtain ⟨g_cand, hg_cand_mem, hg_cand_eq, hg_cand_bound⟩ := hfoldr

  have hsum : ((List.finRange n).map (fun j => α j)).sum = ∑ i, α i := by
    exact (Fin.sum_univ_def α).symm

  have hg_cand_eq' : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 (iteratedDistribDeriv n α u)) φ =
        ∫ ξ, (sobolevWeight n (m - ↑(∑ i, α i)) ξ : ℂ)⁻¹ * g_cand ξ * φ ξ := by
    intro φ
    have h := hg_cand_eq φ
    simp only [iteratedDistribDeriv] at h ⊢
    exact h

  have hint_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ∫ ξ, (sobolevWeight n (m - ↑(∑ i, α i)) ξ : ℂ)⁻¹ * g' ξ * φ ξ =
      ∫ ξ, (sobolevWeight n (m - ↑(∑ i, α i)) ξ : ℂ)⁻¹ * g_cand ξ * φ ξ := by
    intro φ; rw [← hg'_eq φ, ← hg_cand_eq' φ]
  have hae : g' =ᵐ[volume] g_cand :=
    sobolev_witness_ae_unique n g' g_cand hg'_mem hg_cand_mem hint_eq

  have hg_cand_bound' : ∀ ξ, ‖g_cand ξ‖ ≤ (2 * Real.pi) ^ (∑ i, α i) * ‖g ξ‖ := by
    intro ξ
    have h := hg_cand_bound ξ
    rwa [hsum] at h
  exact hae.mono (fun ξ hξ => by rw [hξ]; exact hg_cand_bound' ξ)

end WitnessAeBound

/-- Quantitative Sobolev bound: the `L^2` witness of `D^α u` has norm at most
`(2π)^{|α|}` times the norm of the witness of `u`. -/
theorem multiIndexDeriv_memHs_norm_bound {m : ℝ}
    (α : Fin n → ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g : EuclideanSpace ℝ (Fin n) → ℂ) (hg : MemLp g 2)
    (hug : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u) φ = ∫ ξ, (sobolevWeight n m ξ : ℂ)⁻¹ * g ξ * φ ξ)
    {g' : EuclideanSpace ℝ (Fin n) → ℂ} (hg'_mem : MemLp g' 2)
    (hg'_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 (iteratedDistribDeriv n α u)) φ =
        ∫ ξ, (sobolevWeight n (m - ↑(∑ i, α i)) ξ : ℂ)⁻¹ * g' ξ * φ ξ) :
    eLpNorm g' 2 volume ≤ ENNReal.ofReal ((2 * Real.pi) ^ (∑ i, α i)) * eLpNorm g 2 volume :=
  eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (iteratedDistribDeriv_witness_ae_bound n α u g hg hug hg'_mem hg'_eq) 2


/-- Continuity of the multi-index derivative `D^α : H^m → H^{m - |α|}` with an
explicit positive operator-norm constant `C = (2π)^{|α|}`. -/
theorem multiIndexDeriv_Hs_continuous {m : ℝ}
    (α : Fin n → ℕ) :
    let s := m - ↑(∑ i, α i)
    ∃ C : ℝ, C > 0 ∧ ∀ (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
      (g : EuclideanSpace ℝ (Fin n) → ℂ) (hg : MemLp g 2)
      (hug : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (𝓕 u) φ = ∫ ξ, (sobolevWeight n m ξ : ℂ)⁻¹ * g ξ * φ ξ),
      ∃ g' : EuclideanSpace ℝ (Fin n) → ℂ, MemLp g' 2 ∧
        (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
          (𝓕 (iteratedDistribDeriv n α u)) φ =
            ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g' ξ * φ ξ) ∧
        eLpNorm g' 2 volume ≤ ENNReal.ofReal C * eLpNorm g 2 volume := by
  intro s
  refine ⟨(2 * Real.pi) ^ (∑ i, α i), by positivity, ?_⟩
  intro u g hg hug
  have hu_memHs : MemHs n m u := ⟨g, hg, hug⟩
  have hderiv := memHs_iteratedDistribDeriv α u hu_memHs
  have hs : m - (↑(multiIndexOrder n α) : ℝ) = s := rfl
  rw [hs] at hderiv
  obtain ⟨g', hg'_mem, hg'_eq⟩ := hderiv
  refine ⟨g', hg'_mem, ?_, ?_⟩
  · exact hg'_eq
  · exact multiIndexDeriv_memHs_norm_bound n α u g hg hug hg'_mem hg'_eq

/-- Combined statement: `D^α` maps `H^m` to `H^{m - |α|}` and is bounded as a linear
operator with explicit constant `(2π)^{|α|}`. This corresponds to Melrose Prop 10.2. -/
theorem iteratedDistribDeriv_memHs_and_bounded {m : ℝ} (α : Fin n → ℕ) :
    (∀ (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)),
      MemHs n m u → MemHs n (m - ↑(∑ i, α i)) (iteratedDistribDeriv n α u)) ∧
    (let s := m - ↑(∑ i, α i)
     ∃ C : ℝ, C > 0 ∧ ∀ (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
       (g : EuclideanSpace ℝ (Fin n) → ℂ) (hg : MemLp g 2)
       (hug : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
         (𝓕 u) φ = ∫ ξ, (sobolevWeight n m ξ : ℂ)⁻¹ * g ξ * φ ξ),
       ∃ g' : EuclideanSpace ℝ (Fin n) → ℂ, MemLp g' 2 ∧
         (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
           (𝓕 (iteratedDistribDeriv n α u)) φ =
             ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g' ξ * φ ξ) ∧
         eLpNorm g' 2 volume ≤ ENNReal.ofReal C * eLpNorm g 2 volume) :=
  ⟨fun u hu => multiIndexDeriv_memHs n α u hu,
   multiIndexDeriv_Hs_continuous n α⟩

end DiffOpSobolev

end
