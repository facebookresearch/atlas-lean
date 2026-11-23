/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Data.Fin.Basic

open InnerProductSpace Submodule Set

namespace SpaceCurves

theorem gram_schmidt_orthonormalization {n k : ℕ} (_hk : k ≤ n)
    (v : Fin k → EuclideanSpace ℝ (Fin n))
    (hli : LinearIndependent ℝ v) :
    ∃ (e : Fin k → EuclideanSpace ℝ (Fin n)),
      Orthonormal ℝ e ∧
      (∀ (i : Fin k),
        Submodule.span ℝ (Set.range (fun j : Fin (i.val + 1) => e ⟨j, by omega⟩)) =
        Submodule.span ℝ (Set.range (fun j : Fin (i.val + 1) => v ⟨j, by omega⟩))) ∧
      (∀ i : Fin k, (0 : ℝ) < @inner ℝ _ _ (e i) (v i)) := by
  refine ⟨gramSchmidtNormed ℝ v, gramSchmidtNormed_orthonormal hli, fun i => ?_, fun i => ?_⟩
  ·
    have heq_e : Set.range (fun j : Fin (i.val + 1) => gramSchmidtNormed ℝ v ⟨j, by omega⟩) =
        gramSchmidtNormed ℝ v '' Set.Iic i := by
      ext x
      simp only [Set.mem_range, Set.mem_image, Set.mem_Iic]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨⟨j.val, by omega⟩, Fin.mk_le_mk.mpr (by omega), rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j.val, by omega⟩, rfl⟩
    have heq_v : Set.range (fun j : Fin (i.val + 1) => v ⟨j, by omega⟩) =
        v '' Set.Iic i := by
      ext x
      simp only [Set.mem_range, Set.mem_image, Set.mem_Iic]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨⟨j.val, by omega⟩, Fin.mk_le_mk.mpr (by omega), rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j.val, by omega⟩, rfl⟩
    rw [heq_e, heq_v, span_gramSchmidtNormed, span_gramSchmidt_Iic]
  ·
    simp only [gramSchmidtNormed, inner_smul_left]
    apply mul_pos
    · exact inv_pos.mpr (norm_pos_iff.mpr (gramSchmidt_ne_zero i hli))
    · have key : @inner ℝ _ _ (gramSchmidt ℝ v i) (v i) = ‖gramSchmidt ℝ v i‖ ^ 2 := by
        conv_rhs => rw [← real_inner_self_eq_norm_sq]
        have hdef := gramSchmidt_def' ℝ v i
        conv_lhs => rw [hdef]
        rw [inner_add_right, inner_sum]
        suffices h : ∑ x ∈ Finset.Iio i,
            @inner ℝ _ _ (gramSchmidt ℝ v i) ((ℝ ∙ gramSchmidt ℝ v x).starProjection (v i)) = 0 by
          linarith
        apply Finset.sum_eq_zero
        intro j hj
        rw [starProjection_singleton, inner_smul_right]
        have hne : (i : Fin k) ≠ j :=
          Ne.symm (Finset.mem_Iio.mp hj).ne
        rw [gramSchmidt_orthogonal ℝ v hne]
        simp
      rw [key]
      exact pow_pos (norm_pos_iff.mpr (gramSchmidt_ne_zero i hli)) 2

theorem gram_schmidt_orthonormalization_unique
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (v : Fin k → E)
    (e₁ e₂ : Fin k → E)
    (hon₁ : Orthonormal ℝ e₁) (hon₂ : Orthonormal ℝ e₂)
    (hspan₁ : ∀ i : Fin k, span ℝ (e₁ '' Iic i) = span ℝ (v '' Iic i))
    (hspan₂ : ∀ i : Fin k, span ℝ (e₂ '' Iic i) = span ℝ (v '' Iic i))
    (hpos₁ : ∀ i, (0 : ℝ) < @inner ℝ _ _ (e₁ i) (v i))
    (hpos₂ : ∀ i, (0 : ℝ) < @inner ℝ _ _ (e₂ i) (v i)) :
    e₁ = e₂ := by
  suffices h : ∀ j : Fin k, e₁ j = e₂ j from funext h
  intro j
  apply Fin.strong_induction_on (motive := fun j => e₁ j = e₂ j)
  intro i ih
  have hmem : e₂ i ∈ span ℝ (e₁ '' Iic i) := by
    rw [hspan₁, ← hspan₂]
    exact subset_span (Set.mem_image_of_mem e₂ (Set.mem_Iic.mpr le_rfl))
  have hort : ∀ m : Fin k, m < i → @inner ℝ _ _ (e₁ m) (e₂ i) = 0 := by
    intro m hm
    rw [ih m hm]
    exact hon₂.2 (ne_of_lt hm)
  set c := @inner ℝ _ _ (e₁ i) (e₂ i) with hc_def
  have hd_zero : e₂ i - c • e₁ i = 0 := by
    have hd_in : e₂ i - c • e₁ i ∈ span ℝ (e₁ '' Iic i) :=
      sub_mem hmem (smul_mem _ _ (subset_span (Set.mem_image_of_mem e₁ (Set.mem_Iic.mpr le_rfl))))
    have hd_ort : e₂ i - c • e₁ i ∈ (span ℝ (e₁ '' Iic i))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
      · rintro x ⟨m, hm_le, rfl⟩
        rw [Set.mem_Iic] at hm_le
        simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real]
        rcases eq_or_lt_of_le hm_le with heq_m | hlt
        · have hmi : m = i := heq_m
          rw [hmi]
          have : @inner ℝ _ _ (e₂ i) (e₁ i) = c := by
            rw [hc_def, real_inner_comm]
          rw [this, show @inner ℝ _ _ (e₁ i) (e₁ i) = (1 : ℝ) from by
            rw [real_inner_self_eq_norm_sq, hon₁.1 i, one_pow]]
          ring
        · rw [show @inner ℝ _ _ (e₂ i) (e₁ m) = (0 : ℝ) from by
            rw [real_inner_comm]; exact hort m hlt]
          rw [show @inner ℝ _ _ (e₁ i) (e₁ m) = (0 : ℝ) from hon₁.2 (ne_of_gt hlt)]
          ring
      · simp
      · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx; rw [inner_smul_right, hx, mul_zero]
    exact Submodule.disjoint_def.mp (Submodule.orthogonal_disjoint _) _ hd_in hd_ort
  have heq : e₂ i = c • e₁ i := sub_eq_zero.mp hd_zero
  have hc_one : c = 1 := by
    have hc_abs : |c| = 1 := by
      have h1 : ‖e₂ i‖ = 1 := hon₂.1 i
      rw [heq, norm_smul, hon₁.1 i, mul_one, Real.norm_eq_abs] at h1
      exact h1
    have hc_pos : (0 : ℝ) < c := by
      have h2 := hpos₂ i
      rw [heq, inner_smul_left, RCLike.conj_to_real] at h2
      exact (mul_pos_iff.mp h2).elim (fun h => h.1)
        (fun h => absurd h.2 (not_lt.mpr (le_of_lt (hpos₁ i))))
    linarith [abs_eq_self.mpr (le_of_lt hc_pos)]
  rw [heq, hc_one, one_smul]

end SpaceCurves

namespace SpaceCurves

lemma OrderedFinpartition.partSize_eq_one_of_length_eq
    {m : ℕ} (p : OrderedFinpartition m) (h : p.length = m) (i : Fin p.length) :
    p.partSize i = 1 := by
  have hcard : Fintype.card ((k : Fin p.length) × Fin (p.partSize k)) = m :=
    (Fintype.card_congr p.equivSigma).trans (Fintype.card_fin m)
  rw [Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin] at hcard
  have hle : ∀ k : Fin p.length, 1 ≤ p.partSize k := fun k => p.partSize_pos k
  have hdecomp : ∑ k : Fin p.length, p.partSize k =
      p.partSize i + ∑ k ∈ Finset.univ.erase i, p.partSize k := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hrest : p.length - 1 ≤ ∑ k ∈ Finset.univ.erase i, p.partSize k := by
    have hcard_erase : (Finset.univ.erase i).card = p.length - 1 := by
      simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
    calc (p.length - 1 : ℕ) = ∑ _k ∈ Finset.univ.erase i, 1 := by
            simp [Finset.sum_const, hcard_erase]
      _ ≤ ∑ k ∈ Finset.univ.erase i, p.partSize k :=
            Finset.sum_le_sum (fun k hk => hle k)
  have hpi := hle i
  have hkey : m = p.partSize i + ∑ k ∈ Finset.univ.erase i, p.partSize k := by
    linarith [hcard, hdecomp]
  omega

theorem span_iteratedDeriv_comp_ge {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (φ : ℝ → ℝ) (hc : ContDiff ℝ ⊤ c) (hφ : ContDiff ℝ ⊤ φ)
    (hφ' : ∀ t, 0 < deriv φ t) (t : ℝ) (j : ℕ) (hj : j < n - 1) :
    iteratedDeriv (j + 1) c (φ t) ∈
      Submodule.span ℝ (Set.range (fun k : Fin (j + 1) =>
        iteratedDeriv (k.val + 1) (c ∘ φ) t)) := by
  induction j using Nat.strongRecOn with
  | ind j ih =>

  have hfdb : iteratedDeriv (j + 1) (c ∘ φ) t =
      ∑ p : OrderedFinpartition (j + 1),
        (∏ m : Fin p.length, iteratedDeriv (p.partSize m) φ t) •
        iteratedDeriv p.length c (φ t) :=
    iteratedDeriv_scomp_eq_sum_orderedFinpartition
      (hc.contDiffAt) (hφ.contDiffAt) (by simp)
  set S := Submodule.span ℝ (Set.range (fun k : Fin (j + 1) =>
      iteratedDeriv (k.val + 1) (c ∘ φ) t))
  have hcomp_in_S : iteratedDeriv (j + 1) (c ∘ φ) t ∈ S :=
    Submodule.subset_span ⟨⟨j, by omega⟩, rfl⟩

  set F := Finset.univ.filter (fun p : OrderedFinpartition (j + 1) => p.length = j + 1)
  set L := Finset.univ.filter (fun p : OrderedFinpartition (j + 1) => p.length ≠ j + 1)

  have hcoeff_eq : ∀ p : OrderedFinpartition (j + 1), p.length = j + 1 →
      (∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t) = (deriv φ t) ^ (j + 1) := by
    intro p hp
    have hall := fun i => OrderedFinpartition.partSize_eq_one_of_length_eq p hp i
    calc ∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t
        = ∏ k : Fin p.length, iteratedDeriv 1 φ t := by
          congr 1; ext k; rw [hall k]
      _ = ∏ k : Fin p.length, deriv φ t := by simp [iteratedDeriv_one]
      _ = (deriv φ t) ^ p.length := by rw [Finset.prod_const, Finset.card_fin]
      _ = (deriv φ t) ^ (j + 1) := by rw [hp]

  have hatomic_in_F : OrderedFinpartition.atomic (j + 1) ∈ F := by
    simp [F, Finset.mem_filter, OrderedFinpartition.atomic_length]

  have hF_sum : ∑ p ∈ F, (∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t) •
      iteratedDeriv p.length c (φ t) =
      ((F.card : ℝ) * (deriv φ t) ^ (j + 1)) • iteratedDeriv (j + 1) c (φ t) := by
    have heach : ∀ p ∈ F, (∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t) •
        iteratedDeriv p.length c (φ t) =
        (deriv φ t) ^ (j + 1) • iteratedDeriv (j + 1) c (φ t) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [hcoeff_eq p hp.2, hp.2]
    rw [Finset.sum_congr rfl heach, Finset.sum_const]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]

  have hlower_in_S : ∑ p ∈ L, (∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t) •
      iteratedDeriv p.length c (φ t) ∈ S := by
    apply Submodule.sum_mem
    intro p hp
    rw [Finset.mem_filter] at hp
    apply Submodule.smul_mem
    have hlen_lt : p.length < j + 1 := by
      have := p.length_le; omega
    have hlen_pos : 0 < p.length :=
      OrderedFinpartition.length_pos p (by omega : 0 < j + 1)
    have hj' : p.length - 1 < j := by omega
    have hj'_bound : p.length - 1 < n - 1 := by omega
    have ih_applied := ih (p.length - 1) hj' hj'_bound
    have hrw : p.length - 1 + 1 = p.length := Nat.sub_add_cancel hlen_pos
    rw [hrw] at ih_applied
    exact Submodule.span_le.mpr (fun x hx => by
      obtain ⟨⟨k, hk⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩) ih_applied

  have hcoeff_ne : (F.card : ℝ) * (deriv φ t) ^ (j + 1) ≠ 0 := by
    apply mul_ne_zero
    · exact Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨_, hatomic_in_F⟩).ne'
    · exact pow_ne_zero _ (ne_of_gt (hφ' t))

  have hsplit : iteratedDeriv (j + 1) (c ∘ φ) t =
      (∑ p ∈ L, (∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t) •
        iteratedDeriv p.length c (φ t)) +
      ((F.card : ℝ) * (deriv φ t) ^ (j + 1)) • iteratedDeriv (j + 1) c (φ t) := by
    rw [← hF_sum, ← Finset.sum_union, hfdb]
    · congr 1
      ext p; simp [F, L, Finset.mem_filter]; tauto
    · exact Finset.disjoint_filter.mpr (fun p _ h1 h2 => h1 h2)

  suffices h : ((F.card : ℝ) * (deriv φ t) ^ (j + 1)) • iteratedDeriv (j + 1) c (φ t) ∈ S by
    exact (Submodule.smul_mem_iff S hcoeff_ne).mp h
  have hkey : ((F.card : ℝ) * (deriv φ t) ^ (j + 1)) • iteratedDeriv (j + 1) c (φ t) =
      iteratedDeriv (j + 1) (c ∘ φ) t -
      ∑ p ∈ L, (∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t) •
        iteratedDeriv p.length c (φ t) := by
    rw [hsplit, add_sub_cancel_left]
  rw [hkey]
  exact Submodule.sub_mem S hcomp_in_S hlower_in_S

end SpaceCurves

open scoped Matrix.Norms.Operator

theorem orthogonal_deriv_skew {n : ℕ} (E : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hE : ContDiff ℝ ⊤ E)
    (horth : ∀ t, E t ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ t, deriv E t = E t * A t) (t : ℝ) :
    (A t).transpose = - A t := by

  have hEEt : E t * (E t).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp (horth t)
  have hEtE : (E t).transpose * E t = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp (horth t)

  have hEdiff : DifferentiableAt ℝ E t :=
    (hE.differentiable WithTop.top_ne_zero).differentiableAt
  let L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hEtdiff : DifferentiableAt ℝ (fun s => (E s).transpose) t :=
    L.differentiableAt.comp t hEdiff

  have hconst : (fun s => E s * (E s).transpose) = Function.const ℝ 1 := by
    funext s; exact (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp (horth s)
  have hderiv_zero : deriv (fun s => E s * (E s).transpose) t = 0 := by
    rw [hconst]; exact deriv_const t 1

  have hprod : deriv (fun s => E s * (E s).transpose) t =
    deriv E t * (E t).transpose + E t * deriv (fun s => (E s).transpose) t :=
    deriv_mul hEdiff hEtdiff

  have hderiv_transpose : deriv (fun s => (E s).transpose) t = (deriv E t).transpose := by
    have hfun : (fun s => (E s).transpose) = L ∘ E := rfl
    rw [hfun, fderiv_comp_deriv t L.differentiableAt hEdiff, ContinuousLinearMap.fderiv]
    rfl

  have key : deriv E t * (E t).transpose + E t * (deriv E t).transpose = 0 := by
    rw [← hderiv_transpose, ← hprod]; exact hderiv_zero

  rw [hA t] at key
  rw [Matrix.transpose_mul] at key
  rw [← Matrix.mul_assoc (E t) ((A t).transpose) _] at key
  rw [← add_mul, ← mul_add] at key


  have hU : IsUnit (E t) := ⟨⟨E t, (E t).transpose, hEEt, hEtE⟩, rfl⟩
  have hUt : IsUnit ((E t).transpose) := ⟨⟨(E t).transpose, E t, hEtE, hEEt⟩, rfl⟩
  have h1 : (A t + (A t).transpose) * (E t).transpose = 0 := by
    apply hU.mul_left_cancel
    rw [mul_zero, ← Matrix.mul_assoc]
    exact key
  have h2 : A t + (A t).transpose = 0 :=
    hUt.mul_right_cancel (c := 0) (by rw [zero_mul]; exact h1)

  have : (A t).transpose = -A t + (A t + (A t).transpose) := by abel
  rw [h2, add_zero] at this
  exact this

namespace SpaceCurves

def IsFrenetCurve {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ContDiff ℝ ⊤ c ∧
  ∀ t, LinearIndependent ℝ (fun i : Fin (n - 1) =>
    iteratedDeriv (i.val + 1) c t)

noncomputable def frenetFrame {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (_hc : IsFrenetCurve c) (t : ℝ) : Fin n → EuclideanSpace ℝ (Fin n) :=
  gramSchmidtOrthonormalBasis finrank_euclideanSpace (fun i : Fin n =>
    if _h : i.val < n - 1 then iteratedDeriv (i.val + 1) c t
    else 0)

noncomputable def frenetCurvature {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (i : Fin (n - 1)) (t : ℝ) : ℝ :=
  @inner ℝ _ _ (frenetFrame c hc t ⟨i.val + 1, by omega⟩)
    (deriv (fun s => frenetFrame c hc s ⟨i.val, by omega⟩) t) /
  ‖deriv c t‖

noncomputable def frenetSerretMatrix {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j : Fin n =>
    if h : j.val = i.val + 1 ∧ i.val < n - 1 then
      -(frenetCurvature c hc ⟨i.val, h.2⟩ t)
    else if h : i.val = j.val + 1 ∧ j.val < n - 1 then
      frenetCurvature c hc ⟨j.val, h.2⟩ t
    else 0)








theorem frenetFrame_inner_deriv_sub {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) (hc' : ‖deriv c t‖ ≠ 0)
    (k j : Fin n) (h1 : ¬(j.val = k.val + 1 ∧ k.val < n - 1))
    (h : k.val = j.val + 1 ∧ j.val < n - 1) :
    @inner ℝ _ _ (frenetFrame c hc t k)
      (deriv (fun s => frenetFrame c hc s j) t) =
    ‖deriv c t‖ * frenetCurvature c hc ⟨j.val, h.2⟩ t := by
  unfold frenetCurvature
  rw [mul_div_cancel₀ _ hc']
  congr 1
  · congr 1
    exact Fin.ext h.1

theorem frenetCurvature_eq_inner_div_norm {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (i : Fin (n - 1)) (t : ℝ) :
    frenetCurvature c hc i t =
    @inner ℝ _ _ (frenetFrame c hc t ⟨i.val + 1, by omega⟩)
      (deriv (fun s => frenetFrame c hc s ⟨i.val, by omega⟩) t) /
    ‖deriv c t‖ := by
  rfl








theorem frenet_diagonal_entry_zero {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) (hc' : ‖deriv c t‖ ≠ 0) :
    @inner ℝ _ _ (frenetFrame c hc t ⟨0, by omega⟩) (iteratedDeriv 1 c t) =
    ‖deriv c t‖ := by
  haveI : NeZero n := ⟨by omega⟩

  set f : Fin n → EuclideanSpace ℝ (Fin n) := fun i =>
    if _h : i.val < n - 1 then iteratedDeriv (i.val + 1) c t else 0 with hf_def
  have hf0 : f ⟨0, by omega⟩ = iteratedDeriv 1 c t := by
    simp [f, show (0 : ℕ) < n - 1 from by omega]

  have hgs0 : gramSchmidt ℝ f ⟨0, by omega⟩ = f ⟨0, by omega⟩ := by
    have hempty : Finset.Iio (⟨0, by omega⟩ : Fin n) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ⟨x, hx⟩
      simp only [Finset.mem_Iio, Fin.lt_def, not_lt, Nat.zero_le]
    rw [gramSchmidt_def, hempty, Finset.sum_empty, sub_zero]
  have hf0_ne : f ⟨0, by omega⟩ ≠ 0 := by
    rw [hf0, iteratedDeriv_one]
    exact fun h => hc' (norm_eq_zero.mpr h)
  have hgsn_ne : gramSchmidtNormed ℝ f ⟨0, by omega⟩ ≠ 0 := by
    simp only [gramSchmidtNormed, hgs0]
    intro h
    have := smul_eq_zero.mp h
    rcases this with hinv | hzero
    · exact absurd (inv_eq_zero.mp hinv) (norm_ne_zero_iff.mpr hf0_ne)
    · exact hf0_ne hzero
  have hframe : frenetFrame c hc t ⟨0, by omega⟩ = gramSchmidtNormed ℝ f ⟨0, by omega⟩ :=
    gramSchmidtOrthonormalBasis_apply finrank_euclideanSpace hgsn_ne
  have hgsn_eq : gramSchmidtNormed ℝ f ⟨0, by omega⟩ = (‖f ⟨0, by omega⟩‖⁻¹ : ℝ) • f ⟨0, by omega⟩ := by
    simp only [gramSchmidtNormed, hgs0]
    norm_cast
  rw [hframe, hgsn_eq, hf0, inner_smul_left, iteratedDeriv_one, real_inner_self_eq_norm_sq]
  simp only [starRingEnd_apply, star_trivial]
  rw [sq, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]



lemma prod_fin_triangular {M : Type*} [CommMonoid M] (n : ℕ) (f : Fin (n - 1) → M) :
    ∏ i : Fin n, ∏ k : Fin i.val, f ⟨k.val, by omega⟩ =
    ∏ k : Fin (n - 1), f k ^ (n - 1 - k.val) := by
  let g : ℕ → M := fun k => if h : k < n - 1 then f ⟨k, h⟩ else 1
  have hlhs : ∏ i : Fin n, ∏ k : Fin i.val, f ⟨k.val, by omega⟩ =
      ∏ i ∈ Finset.range n, ∏ k ∈ Finset.range i, g k := by
    rw [← Fin.prod_univ_eq_prod_range]
    congr 1; ext i
    rw [← Fin.prod_univ_eq_prod_range]
    congr 1; ext k
    simp only [g]
    rw [dif_pos (by omega : k.val < n - 1)]
  have hrhs : ∏ k : Fin (n - 1), f k ^ (n - 1 - k.val) =
      ∏ k ∈ Finset.range (n - 1), g k ^ (n - 1 - k) := by
    rw [← Fin.prod_univ_eq_prod_range]
    congr 1; ext k
    simp only [g]
    rw [dif_pos k.isLt]
  rw [hlhs, hrhs]
  have swap : ∏ i ∈ Finset.range n, ∏ k ∈ Finset.range i, g k =
      ∏ k ∈ Finset.range (n - 1), ∏ i ∈ (Finset.range n).filter (fun i => k < i), g k := by
    apply Finset.prod_comm'
    intro x y
    simp only [Finset.mem_range, Finset.mem_filter]
    omega
  rw [swap]
  congr 1; ext k
  rw [Finset.prod_const]
  congr 1
  have h : Finset.filter (fun i => k < i) (Finset.range n) = Finset.Ico (k + 1) n := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [h, Nat.card_Ico]
  omega

theorem frenet_product_reindex {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) :
    ∏ i : Fin n, ∏ k : Fin i.val,
      frenetCurvature c hc ⟨k.val, by omega⟩ t =
    ∏ i : Fin (n - 1), frenetCurvature c hc i t ^ (n - 1 - i.val) :=
  prod_fin_triangular n (fun k => frenetCurvature c hc k t)






lemma linearIndependent_of_span_eq {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (v w : Fin k → V)
    (hv : LinearIndependent ℝ v)
    (heq : Submodule.span ℝ (Set.range w) = Submodule.span ℝ (Set.range v)) :
    LinearIndependent ℝ w := by
  set S := Submodule.span ℝ (Set.range v)
  have hfinrank_S : Module.finrank ℝ S = k := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  have hw_mem : ∀ i, w i ∈ S := fun i => by
    have : w i ∈ Submodule.span ℝ (Set.range w) := Submodule.subset_span ⟨i, rfl⟩
    rwa [heq] at this
  set w' : Fin k → S := fun i => ⟨w i, hw_mem i⟩
  have hspan_top : ⊤ ≤ Submodule.span ℝ (Set.range w') := by
    suffices h : ∀ x : S, x ∈ Submodule.span ℝ (Set.range w') from fun x _ => h x
    intro ⟨x, hx⟩
    have hx_in_w : x ∈ Submodule.span ℝ (Set.range w) := heq ▸ hx
    have hrange_le : Set.range w ⊆ S.subtype '' (Set.range w') := by
      rintro y ⟨i, rfl⟩
      exact ⟨w' i, Set.mem_range.mpr ⟨i, rfl⟩, rfl⟩
    have hmono : Submodule.span ℝ (Set.range w) ≤
        (Submodule.span ℝ (Set.range w')).map S.subtype := by
      apply Submodule.span_le.mpr
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hrange_le hy
      exact Submodule.mem_map.mpr ⟨z, Submodule.subset_span hz, rfl⟩
    have hx_mapped := hmono hx_in_w
    rw [Submodule.mem_map] at hx_mapped
    obtain ⟨z, hz, hze⟩ := hx_mapped
    have : z = ⟨x, hx⟩ := Subtype.ext hze
    rw [← this]
    exact hz
  have hli' : LinearIndependent ℝ w' :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan_top
      (by rw [Fintype.card_fin, hfinrank_S])
  exact hli'.map' S.subtype (Submodule.ker_subtype S)

theorem frenet_reparametrization_isFrenet {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (φ : ℝ → ℝ) (hc : IsFrenetCurve c) (hφ : ContDiff ℝ ⊤ φ)
    (hφ' : ∀ t, 0 < deriv φ t) :
    IsFrenetCurve (c ∘ φ) := by
  refine ⟨hc.1.comp hφ, fun t => ?_⟩
  set w := fun i : Fin (n - 1) => iteratedDeriv (i.val + 1) (c ∘ φ) t
  set v := fun i : Fin (n - 1) => iteratedDeriv (i.val + 1) c (φ t)
  have hv_li : LinearIndependent ℝ v := hc.2 (φ t)

  have hle : Submodule.span ℝ (Set.range w) ≤ Submodule.span ℝ (Set.range v) := by
    apply Submodule.span_le.mpr
    rintro x ⟨⟨k, hk⟩, rfl⟩
    show iteratedDeriv (k + 1) (c ∘ φ) t ∈ _
    have hfdb : iteratedDeriv (k + 1) (c ∘ φ) t =
        ∑ p : OrderedFinpartition (k + 1),
          (∏ m : Fin p.length, iteratedDeriv (p.partSize m) φ t) •
          iteratedDeriv p.length c (φ t) :=
      iteratedDeriv_scomp_eq_sum_orderedFinpartition
        (hc.1.contDiffAt) (hφ.contDiffAt) (by simp)
    rw [hfdb]
    apply Submodule.sum_mem
    intro p _
    apply Submodule.smul_mem
    have hlen_pos : 0 < p.length :=
      OrderedFinpartition.length_pos p (by omega : 0 < k + 1)
    have hlen_le : p.length ≤ k + 1 := p.length_le
    exact Submodule.subset_span ⟨⟨p.length - 1, by omega⟩,
      by simp only [v, Nat.sub_one_add_one_eq_of_pos hlen_pos]⟩

  have hge : Submodule.span ℝ (Set.range v) ≤ Submodule.span ℝ (Set.range w) := by
    apply Submodule.span_le.mpr
    rintro x ⟨⟨k, hk⟩, rfl⟩
    show iteratedDeriv (k + 1) c (φ t) ∈ _
    have h := span_iteratedDeriv_comp_ge c φ hc.1 hφ hφ' t k hk
    exact Submodule.span_le.mpr (fun y hy => by
      obtain ⟨⟨j, hj⟩, rfl⟩ := hy
      exact Submodule.subset_span ⟨⟨j, by omega⟩, rfl⟩) h
  exact linearIndependent_of_span_eq v w hv_li (le_antisymm hle hge)






set_option maxHeartbeats 800000 in
theorem span_iteratedDeriv_comp_eq_Iic {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (φ : ℝ → ℝ) (hc : ContDiff ℝ ⊤ c) (hφ : ContDiff ℝ ⊤ φ)
    (hφ' : ∀ t, 0 < deriv φ t) (t : ℝ) (i : Fin (n - 1)) :
    span ℝ ((fun j : Fin (n - 1) => iteratedDeriv (j.val + 1) (c ∘ φ) t) '' Iic i) =
    span ℝ ((fun j : Fin (n - 1) => iteratedDeriv (j.val + 1) c (φ t)) '' Iic i) := by
  apply le_antisymm
  ·
    apply Submodule.span_le.mpr
    rintro x ⟨k, hk, rfl⟩
    have hk_le := Fin.le_iff_val_le_val.mp (Set.mem_Iic.mp hk)


    show iteratedDeriv (k.val + 1) (c ∘ φ) t ∈ _
    have hfdb : iteratedDeriv (k.val + 1) (c ∘ φ) t =
        ∑ p : OrderedFinpartition (k.val + 1),
          (∏ m : Fin p.length, iteratedDeriv (p.partSize m) φ t) •
          iteratedDeriv p.length c (φ t) :=
      iteratedDeriv_scomp_eq_sum_orderedFinpartition (hc.contDiffAt) (hφ.contDiffAt) (by simp)
    rw [hfdb]
    apply Submodule.sum_mem
    intro p _
    apply Submodule.smul_mem
    have hlen_pos : 0 < p.length := OrderedFinpartition.length_pos p (by omega : 0 < k.val + 1)
    have hlen_le : p.length ≤ k.val + 1 := p.length_le
    apply Submodule.subset_span
    refine ⟨⟨p.length - 1, by omega⟩, Set.mem_Iic.mpr (Fin.mk_le_mk.mpr (by omega)), ?_⟩
    simp only [Nat.sub_one_add_one_eq_of_pos hlen_pos]
  ·
    apply Submodule.span_le.mpr
    rintro x ⟨k, hk, rfl⟩
    have hk_le := Fin.le_iff_val_le_val.mp (Set.mem_Iic.mp hk)
    show iteratedDeriv (k.val + 1) c (φ t) ∈ _
    have h := span_iteratedDeriv_comp_ge c φ hc hφ hφ' t k.val k.isLt


    exact Submodule.span_le.mpr (fun y hy => by
      obtain ⟨⟨j, hj⟩, rfl⟩ := hy
      apply Submodule.subset_span
      exact ⟨⟨j, by omega⟩, Set.mem_Iic.mpr (Fin.mk_le_mk.mpr (by omega)), rfl⟩) h






end SpaceCurves
