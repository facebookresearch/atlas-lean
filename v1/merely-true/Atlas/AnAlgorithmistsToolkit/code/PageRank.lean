/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Data.Real.Basic

open scoped Matrix BigOperators
open Matrix Finset

namespace PageRank

variable {n : ℕ}

noncomputable def pageRankVec (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) :
    Fin n → ℝ :=
  ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹ *ᵥ (α • s)

theorem pageRankVec_fixed_point (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ)
    (hW : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)) :
    pageRankVec α W s = α • s + (1 - α) • (W *ᵥ (pageRankVec α W s)) := by
  set M := (1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W with hM_def
  set x := pageRankVec α W s

  suffices h : x - (1 - α) • (W *ᵥ x) = α • s from
    eq_add_of_sub_eq h
  have hMx : M *ᵥ x = α • s := by
    show M *ᵥ (M⁻¹ *ᵥ (α • s)) = α • s
    rw [mulVec_mulVec, mul_nonsing_inv _ (hW.map Matrix.detMonoidHom), one_mulVec]
  rw [← hMx]
  simp only [M, sub_mulVec, one_mulVec, smul_mulVec]

theorem pageRankVec_unique (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ)
    (hW : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W))
    (x : Fin n → ℝ) (hx : x = α • s + (1 - α) • (W *ᵥ x)) :
    x = pageRankVec α W s := by
  set M := (1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W with hM_def

  have hMx : M *ᵥ x = α • s := by
    have hM_expand : M *ᵥ x = x - (1 - α) • (W *ᵥ x) := by
      simp only [M, sub_mulVec, one_mulVec, smul_mulVec]
    rw [hM_expand]
    have hsub : x - (1 - α) • (W *ᵥ x) = α • s := sub_eq_of_eq_add hx
    exact hsub

  show x = M⁻¹ *ᵥ (α • s)
  calc x = (M⁻¹ * M) *ᵥ x := by
          rw [nonsing_inv_mul _ (hW.map Matrix.detMonoidHom), one_mulVec]
    _ = M⁻¹ *ᵥ (M *ᵥ x) := by rw [mulVec_mulVec]
    _ = M⁻¹ *ᵥ (α • s) := by rw [hMx]

theorem pageRankVec_comm_W (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ)
    (hcomm : Commute W ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹) :
    pageRankVec α W (W *ᵥ s) = W *ᵥ (pageRankVec α W s) := by
  set M_inv := ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹
  show M_inv *ᵥ (α • (W *ᵥ s)) = W *ᵥ (M_inv *ᵥ (α • s))
  simp_rw [Matrix.mulVec_smul]
  congr 1
  rw [mulVec_mulVec, mulVec_mulVec, hcomm.eq]

theorem pageRankVec_comm_W_of_isUnit (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ)
    (hW : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)) :
    pageRankVec α W (W *ᵥ s) = W *ᵥ (pageRankVec α W s) := by
  set x' := W *ᵥ (pageRankVec α W s)
  have hfp : x' = α • (W *ᵥ s) + (1 - α) • (W *ᵥ x') := by
    show W *ᵥ (pageRankVec α W s) = α • (W *ᵥ s) + (1 - α) • (W *ᵥ (W *ᵥ (pageRankVec α W s)))
    have key : α • (W *ᵥ s) + (1 - α) • (W *ᵥ (W *ᵥ (pageRankVec α W s)))
             = W *ᵥ (α • s + (1 - α) • (W *ᵥ (pageRankVec α W s))) := by
      simp only [mulVec_add, Matrix.mulVec_smul, mulVec_mulVec]
    rw [key, ← pageRankVec_fixed_point α W s hW]
  exact (pageRankVec_unique α W (W *ᵥ s) hW x' hfp).symm

theorem pageRankVec_eq2 (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ)
    (hW : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W))
    (hcomm : Commute W ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹) :
    pageRankVec α W s = α • s + (1 - α) • pageRankVec α W (W *ᵥ s) := by
  rw [pageRankVec_comm_W α W s hcomm]
  exact pageRankVec_fixed_point α W s hW

theorem pageRankVec_add (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (s₁ s₂ : Fin n → ℝ) :
    pageRankVec α W (s₁ + s₂) = pageRankVec α W s₁ + pageRankVec α W s₂ := by
  unfold pageRankVec
  rw [smul_add, mulVec_add]

theorem pageRankVec_smul (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (s : Fin n → ℝ) :
    pageRankVec α W (c • s) = c • pageRankVec α W s := by
  show ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹ *ᵥ (α • (c • s)) =
       c • (((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹ *ᵥ (α • s))
  rw [show α • (c • s) = c • (α • s) from smul_comm α c s, mulVec_smul]

theorem pageRankVec_linear (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (c d : ℝ) (v w : Fin n → ℝ) :
    pageRankVec α W (c • v + d • w) = c • pageRankVec α W v + d • pageRankVec α W w := by
  rw [pageRankVec_add, pageRankVec_smul, pageRankVec_smul]

theorem pageRankVec_sub (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (s₁ s₂ : Fin n → ℝ) :
    pageRankVec α W (s₁ - s₂) = pageRankVec α W s₁ - pageRankVec α W s₂ := by
  unfold pageRankVec
  rw [smul_sub, mulVec_sub]

theorem pageRankVec_invariant_preserved
    (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (s p r : Fin n → ℝ) (u : Fin n)
    (hW : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W))
    (hcomm : Commute W ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹)
    (hinv : p = pageRankVec α W (s - r)) :
    let χ_u : Fin n → ℝ := Pi.single u 1
    let p' := p + (α * r u) • χ_u
    let r' := r - r u • χ_u + ((1 - α) * r u) • (W *ᵥ χ_u)
    p' = pageRankVec α W (s - r') := by
  intro χ_u p' r'

  have hinv_sum : p + pageRankVec α W r = pageRankVec α W s := by
    rw [hinv, pageRankVec_sub, sub_add_cancel]


  have hkey : pageRankVec α W r = (α * r u) • χ_u + pageRankVec α W r' := by

    have hr_split : r = (r - r u • χ_u) + r u • χ_u := by
      ext i; simp [sub_add_cancel]

    have h1 : pageRankVec α W r =
        pageRankVec α W (r - r u • χ_u) + pageRankVec α W (r u • χ_u) := by
      conv_lhs => rw [hr_split]
      exact pageRankVec_add α W _ _

    have h2 : pageRankVec α W (r u • χ_u) = r u • pageRankVec α W χ_u := by
      exact pageRankVec_smul α W (r u) χ_u

    have h3 : pageRankVec α W χ_u = α • χ_u + (1 - α) • pageRankVec α W (W *ᵥ χ_u) := by
      exact pageRankVec_eq2 α W χ_u hW hcomm

    rw [h2, h3] at h1


    have h4 : r u • (α • χ_u + (1 - α) • pageRankVec α W (W *ᵥ χ_u)) =
        (α * r u) • χ_u + ((1 - α) * r u) • pageRankVec α W (W *ᵥ χ_u) := by
      rw [smul_add, smul_comm (r u) α, smul_smul, smul_comm (r u) (1 - α), smul_smul]
    rw [h4] at h1


    have h5 : ((1 - α) * r u) • pageRankVec α W (W *ᵥ χ_u) =
        pageRankVec α W (((1 - α) * r u) • (W *ᵥ χ_u)) := by
      exact (pageRankVec_smul α W ((1 - α) * r u) (W *ᵥ χ_u)).symm
    rw [h5] at h1


    have h6 : pageRankVec α W (r - r u • χ_u) + pageRankVec α W (((1 - α) * r u) • (W *ᵥ χ_u)) =
        pageRankVec α W r' := by
      rw [← pageRankVec_add]

    rw [show pageRankVec α W (r - r u • χ_u) + ((α * r u) • χ_u + pageRankVec α W (((1 - α) * r u) • (W *ᵥ χ_u)))
        = (α * r u) • χ_u + (pageRankVec α W (r - r u • χ_u) + pageRankVec α W (((1 - α) * r u) • (W *ᵥ χ_u)))
        from by abel] at h1
    rw [h6] at h1
    exact h1


  have hgoal : p' + pageRankVec α W r' = pageRankVec α W s := by
    rw [show p' = p + (α * r u) • χ_u from rfl]
    rw [show p + (α * r u) • χ_u + pageRankVec α W r' =
        p + ((α * r u) • χ_u + pageRankVec α W r') from add_assoc _ _ _]
    rw [← hkey]
    exact hinv_sum

  rw [pageRankVec_sub]
  exact eq_sub_of_add_eq hgoal

noncomputable def l1norm (f : Fin n → ℝ) : ℝ := ∑ i, |f i|

lemma l1norm_add_le (f g : Fin n → ℝ) : l1norm (f + g) ≤ l1norm f + l1norm g := by
  unfold l1norm
  calc ∑ i, |(f + g) i| ≤ ∑ i, (|f i| + |g i|) :=
        Finset.sum_le_sum (fun i _ => abs_add_le (f i) (g i))
    _ = ∑ i, |f i| + ∑ i, |g i| := Finset.sum_add_distrib

lemma l1norm_smul (c : ℝ) (f : Fin n → ℝ) : l1norm (c • f) = |c| * l1norm f := by
  unfold l1norm
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  rw [Finset.mul_sum]

lemma sum_mul_pi_single (W : Matrix (Fin n) (Fin n) ℝ) (i u : Fin n) :
    ∑ x, W i x * (Pi.single u 1 : Fin n → ℝ) x = W i u := by
  rw [Finset.sum_eq_single u]
  · simp [Pi.single_eq_same]
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ u) h

lemma l1norm_sub_single (r : Fin n → ℝ) (u : Fin n) (hr : ∀ i, 0 ≤ r i) :
    let χ_u : Fin n → ℝ := Pi.single u 1
    l1norm (r - r u • χ_u) = l1norm r - r u := by
  intro χ_u
  unfold l1norm
  have key : ∀ i : Fin n, |(r - r u • χ_u) i| = |r i| - (r u • χ_u) i := by
    intro i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, χ_u]
    by_cases hi : i = u
    · subst hi; simp only [Pi.single_eq_same, mul_one]; simp [abs_of_nonneg (hr i)]
    · simp only [Pi.single_eq_of_ne hi, mul_zero, sub_zero]
  simp_rw [key]
  rw [Finset.sum_sub_distrib]
  suffices h : ∑ i : Fin n, (r u • χ_u) i = r u by linarith
  simp only [Pi.smul_apply, smul_eq_mul, χ_u]
  rw [← Finset.mul_sum]
  simp [Finset.sum_pi_single']

lemma l1norm_mulVec_single_le (W : Matrix (Fin n) (Fin n) ℝ) (u : Fin n)
    (hW : W ∈ colStochastic ℝ (Fin n)) :
    let χ_u : Fin n → ℝ := Pi.single u 1
    l1norm (W *ᵥ χ_u) ≤ 1 := by
  intro χ_u
  unfold l1norm
  have hWnn : ∀ i j, 0 ≤ W i j := hW.1
  have hWcol : ∀ j, ∑ i, W i j = 1 := (mem_colStochastic_iff_sum.mp hW).2
  have hmul : ∀ i, (W *ᵥ χ_u) i = W i u := by
    intro i; simp only [mulVec, dotProduct, χ_u]; exact sum_mul_pi_single W i u
  conv_lhs => arg 2; ext i; rw [hmul i, abs_of_nonneg (hWnn i u)]
  exact le_of_eq (hWcol u)

theorem residual_decrease_bound
    (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (u : Fin n)
    (hα : 0 < α) (hα1 : α < 1)
    (hW : W ∈ colStochastic ℝ (Fin n))
    (hr : ∀ i, 0 ≤ r i) :
    let χ_u : Fin n → ℝ := Pi.single u 1
    let r' := r - r u • χ_u + ((1 - α) * r u) • (W *ᵥ χ_u)
    l1norm r' ≤ l1norm r - α * r u := by
  intro χ_u r'
  have hα_pos := hα
  have h1α_pos : (0 : ℝ) < 1 - α := by linarith

  have h1 : l1norm r' ≤ l1norm (r - r u • χ_u) + l1norm (((1 - α) * r u) • (W *ᵥ χ_u)) :=
    l1norm_add_le (r - r u • χ_u) (((1 - α) * r u) • (W *ᵥ χ_u))

  have h2 : l1norm (r - r u • χ_u) = l1norm r - r u := l1norm_sub_single r u hr

  have h3 : l1norm (((1 - α) * r u) • (W *ᵥ χ_u)) = (1 - α) * r u * l1norm (W *ᵥ χ_u) := by
    rw [l1norm_smul, abs_of_nonneg (mul_nonneg (le_of_lt h1α_pos) (hr u))]

  have h5 : l1norm (W *ᵥ χ_u) ≤ 1 := l1norm_mulVec_single_le W u hW

  have hle : l1norm (((1 - α) * r u) • (W *ᵥ χ_u)) ≤ (1 - α) * r u := by
    rw [h3]
    have : (1 - α) * r u * l1norm (W *ᵥ χ_u) ≤ (1 - α) * r u * 1 :=
      mul_le_mul_of_nonneg_left h5 (mul_nonneg (le_of_lt h1α_pos) (hr u))
    linarith
  linarith

noncomputable def vol (d : Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∑ x ∈ S, d x

noncomputable def vecSupp (f : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => f v ≠ 0)

lemma telescope_decrease {T : ℕ}
    (a : Fin (T + 1) → ℝ) (b : Fin T → ℝ)
    (h : ∀ i : Fin T, a ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ≤
      a ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ - b i) :
    a ⟨T, Nat.lt_succ_iff.mpr le_rfl⟩ ≤ a ⟨0, Nat.zero_lt_succ T⟩ - ∑ i : Fin T, b i := by
  induction T with
  | zero => simp
  | succ T' ih =>
    have h_last := h ⟨T', Nat.lt_succ_iff.mpr le_rfl⟩
    have ih' := ih (fun i => a ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ _)⟩)
        (fun i => b ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ _)⟩)
        (fun i => by exact h ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ _)⟩)
    have h_sum : ∑ i : Fin (T' + 1), b i =
        (∑ i : Fin T', b ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ _)⟩) +
        b ⟨T', Nat.lt_succ_iff.mpr le_rfl⟩ := by
      rw [Fin.sum_univ_castSucc]; congr 1
    rw [h_sum]
    linarith

theorem pageRank_iteration_bound
    (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (T : ℕ)
    (d : Fin n → ℝ) (hd : ∀ v, 1 ≤ d v)

    (residual_norms : Fin (T + 1) → ℝ)
    (h_nonneg : ∀ i, 0 ≤ residual_norms i)

    (vertices : Fin T → Fin n)

    (residual_vals : Fin T → ℝ)

    (h_select : ∀ i : Fin T, ε * d (vertices i) ≤ residual_vals i)

    (h_decrease : ∀ i : Fin T, residual_norms ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ≤
      residual_norms ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ - α * residual_vals i) :
    (T : ℝ) * (α * ε) ≤ residual_norms ⟨0, Nat.zero_lt_succ T⟩ := by

  have h_min_decrease : ∀ i : Fin T,
      residual_norms ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ≤
      residual_norms ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ - α * ε := by
    intro i
    have hεd : ε ≤ residual_vals i :=
      calc ε = ε * 1 := (mul_one ε).symm
        _ ≤ ε * d (vertices i) := by gcongr; exact hd (vertices i)
        _ ≤ residual_vals i := h_select i
    linarith [h_decrease i, mul_le_mul_of_nonneg_left hεd (le_of_lt hα)]

  have h_tel := telescope_decrease residual_norms (fun _ => α * ε) h_min_decrease
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at h_tel

  linarith [h_nonneg ⟨T, Nat.lt_succ_iff.mpr le_rfl⟩]

theorem pageRank_degree_sum_bound
    (α ε : ℝ) (hα : 0 < α)
    (T : ℕ) (d : Fin n → ℝ)
    (residual_norms : Fin (T + 1) → ℝ)
    (h_nonneg : ∀ i, 0 ≤ residual_norms i)
    (vertices : Fin T → Fin n)
    (residual_vals : Fin T → ℝ)
    (h_select : ∀ i : Fin T, ε * d (vertices i) ≤ residual_vals i)
    (h_decrease : ∀ i : Fin T, residual_norms ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ≤
      residual_norms ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ - α * residual_vals i) :
    α * ε * ∑ i : Fin T, d (vertices i) ≤ residual_norms ⟨0, Nat.zero_lt_succ T⟩ := by

  have h_tel := telescope_decrease residual_norms
      (fun i => α * residual_vals i) h_decrease

  have h_sum_le : α * ε * ∑ i : Fin T, d (vertices i) ≤ ∑ i : Fin T, α * residual_vals i := by
    calc α * ε * ∑ i : Fin T, d (vertices i)
        = ∑ i : Fin T, α * (ε * d (vertices i)) := by rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≤ ∑ i : Fin T, α * residual_vals i :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h_select i) (le_of_lt hα))
  linarith [h_nonneg ⟨T, Nat.lt_succ_iff.mpr le_rfl⟩]

theorem vol_supp_le_degree_sum
    (d : Fin n → ℝ) (hd : ∀ v, 0 ≤ d v)
    (p : Fin n → ℝ) (T : ℕ) (vertices : Fin T → Fin n)
    (h_supp_covered : ∀ v ∈ vecSupp p, ∃ i : Fin T, vertices i = v) :
    vol d (vecSupp p) ≤ ∑ i : Fin T, d (vertices i) := by
  classical
  unfold vol
  have h_sub : vecSupp p ⊆ Finset.univ.image vertices := by
    intro v hv
    obtain ⟨i, hi⟩ := h_supp_covered v hv
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  calc ∑ x ∈ vecSupp p, d x
      ≤ ∑ x ∈ Finset.univ.image vertices, d x :=
        Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => hd _)
    _ ≤ ∑ i ∈ Finset.univ, d (vertices i) :=
        Finset.sum_image_le_of_nonneg (fun u _ => hd u)

theorem pageRank_output_quality
    (ε : ℝ) (d : Fin n → ℝ) (r : Fin n → ℝ)
    (hd_pos : ∀ v, 0 < d v)
    (h_term : ∀ v : Fin n, r v < ε * d v) :
    ∀ v : Fin n, r v / d v < ε := by
  intro v
  rw [div_lt_iff₀ (hd_pos v)]
  exact h_term v

theorem pageRank_termination
    (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (T : ℕ)
    (d : Fin n → ℝ) (hd : ∀ v, 1 ≤ d v)
    (p : Fin n → ℝ) (r_final : Fin n → ℝ)

    (residual_norms : Fin (T + 1) → ℝ)
    (h_init : residual_norms ⟨0, Nat.zero_lt_succ T⟩ = 1)
    (h_nonneg : ∀ i, 0 ≤ residual_norms i)

    (vertices : Fin T → Fin n)

    (residual_vals : Fin T → ℝ)

    (h_select : ∀ i : Fin T, ε * d (vertices i) ≤ residual_vals i)

    (h_decrease : ∀ i : Fin T, residual_norms ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ≤
      residual_norms ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ - α * residual_vals i)

    (h_term : ∀ v : Fin n, r_final v < ε * d v)

    (h_supp_covered : ∀ v ∈ vecSupp p, ∃ i : Fin T, vertices i = v) :


    (T : ℝ) * (α * ε) ≤ 1

    ∧ (∀ v : Fin n, r_final v / d v < ε)

    ∧ α * ε * vol d (vecSupp p) ≤ 1 := by
  have hd_nonneg : ∀ v, 0 ≤ d v := fun v => le_trans (by norm_num : (0 : ℝ) ≤ 1) (hd v)
  have hd_pos : ∀ v, 0 < d v := fun v => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hd v)
  refine ⟨?_, ?_, ?_⟩
  ·
    have h := pageRank_iteration_bound α ε hα hε T d hd residual_norms h_nonneg
        vertices residual_vals h_select h_decrease
    linarith [h_init.symm ▸ h]
  ·
    exact pageRank_output_quality ε d r_final hd_pos h_term
  ·
    have h_vol := vol_supp_le_degree_sum d hd_nonneg p T vertices h_supp_covered
    have h_deg := pageRank_degree_sum_bound α ε hα T d residual_norms h_nonneg
        vertices residual_vals h_select h_decrease
    have hαε_pos : (0 : ℝ) < α * ε := mul_pos hα hε
    calc α * ε * vol d (vecSupp p)
        ≤ α * ε * ∑ i : Fin T, d (vertices i) := by
          gcongr
      _ ≤ residual_norms ⟨0, Nat.zero_lt_succ T⟩ := h_deg
      _ = 1 := h_init

end PageRank
