/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Theorems
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace BooleanFourier

open Finset Real

def restrict {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) :
    (Fin n → Bool) → Bool :=
  fun y => f (Fin.cons b y)

lemma card_filter_cons {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) :
    ((Finset.univ.filter fun x : Fin (n + 1) → Bool => x 0 = b ∧ f x = true)).card =
    (Finset.univ.filter fun y : Fin n → Bool => f (Fin.cons b y) = true).card := by
  symm
  apply Finset.card_bij (fun (y : Fin n → Bool) _ => Fin.cons (n := n) (α := fun _ => Bool) b y)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact ⟨(Fin.cons_zero (n := n) (α := fun _ => Bool) b y).symm, hy⟩
  · intro a1 _ a2 _ h
    exact (@Fin.cons_right_injective n (fun _ => Bool) b).eq_iff.mp h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨Fin.tail x, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : Fin.cons b (Fin.tail x) = x := by
        rw [← hx.1]; exact Fin.cons_self_tail x
      rw [this]; exact hx.2
    · have : Fin.cons b (Fin.tail x) = x := by
        rw [← hx.1]; exact Fin.cons_self_tail x
      exact this

lemma filter_card_decomp {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) :
    (Finset.univ.filter fun x => f x = true).card =
    (Finset.univ.filter fun y : Fin n → Bool => f (Fin.cons false y) = true).card +
    (Finset.univ.filter fun y : Fin n → Bool => f (Fin.cons true y) = true).card := by
  have hpart : (Finset.univ.filter fun x : Fin (n + 1) → Bool => f x = true) =
    (Finset.univ.filter fun x : Fin (n + 1) → Bool => x 0 = false ∧ f x = true) ∪
    (Finset.univ.filter fun x : Fin (n + 1) → Bool => x 0 = true ∧ f x = true) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hfx; cases hx0 : x 0 <;> simp [hfx]
    · rintro (⟨_, hfx⟩ | ⟨_, hfx⟩) <;> exact hfx
  have hdisj : Disjoint
    (Finset.univ.filter fun x : Fin (n + 1) → Bool => x 0 = false ∧ f x = true)
    (Finset.univ.filter fun x : Fin (n + 1) → Bool => x 0 = true ∧ f x = true) := by
    apply Finset.disjoint_filter.mpr
    intro x _ ⟨h1, _⟩ ⟨h2, _⟩
    simp [h1] at h2
  rw [hpart, Finset.card_union_of_disjoint hdisj]
  congr 1
  · exact card_filter_cons f false
  · exact card_filter_cons f true

theorem vol_restrict_decomp {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) :
    vol f = (vol (restrict f false) + vol (restrict f true)) / 2 := by
  unfold vol restrict
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hcard := filter_card_decomp f
  rw [show (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n from by ring]
  field_simp
  push_cast [hcard]
  ring


lemma filter_card_split_by_first_coord {n : ℕ}
    (P : (Fin (n+1) → Bool) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
    (Finset.univ.filter fun y : Fin n → Bool => P (Fin.cons false y)).card +
    (Finset.univ.filter fun y : Fin n → Bool => P (Fin.cons true y)).card := by
  classical
  let e : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) := {
    toFun := fun x => (x 0, Fin.tail x)
    invFun := fun p => Fin.cons p.1 p.2
    left_inv := fun x => by ext i; cases i using Fin.cases <;> simp [Fin.tail]
    right_inv := fun p => by ext <;> simp [Fin.tail]
  }
  have h1 : (Finset.univ.filter P).card =
      (Finset.univ.filter fun (p : Bool × (Fin n → Bool)) => P (Fin.cons p.1 p.2)).card := by
    apply Finset.card_equiv e
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hP; have : Fin.cons (e x).1 (e x).2 = x := e.symm_apply_apply x; rwa [this]
    · intro hP; convert hP using 1; exact (e.symm_apply_apply x).symm
  rw [h1]
  have h_disj : Disjoint
      (((Finset.univ : Finset (Fin n → Bool)).filter (fun y => P (Fin.cons false y))).map
        ⟨fun y => (false, y), fun _ _ h => by simpa using h⟩)
      (((Finset.univ : Finset (Fin n → Bool)).filter (fun y => P (Fin.cons true y))).map
        ⟨fun y => (true, y), fun _ _ h => by simpa using h⟩) := by
    rw [Finset.disjoint_left]
    intro ⟨b, y⟩ h1 h2
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at h1 h2
    obtain ⟨_, _, heq₁⟩ := h1
    obtain ⟨_, _, heq₂⟩ := h2
    have hfalse := (Prod.mk.inj heq₁).1
    have htrue := (Prod.mk.inj heq₂).1
    rw [← hfalse] at htrue
    exact absurd htrue.symm Bool.false_ne_true
  have h2 : (Finset.univ : Finset (Bool × (Fin n → Bool))).filter
      (fun p => P (Fin.cons p.1 p.2)) =
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun y => P (Fin.cons false y))).map
        ⟨fun y => (false, y), fun _ _ h => by simpa using h⟩ ∪
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun y => P (Fin.cons true y))).map
        ⟨fun y => (true, y), fun _ _ h => by simpa using h⟩ := by
    ext ⟨b, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro hP; cases b
      · left; exact ⟨y, hP, rfl⟩
      · right; exact ⟨y, hP, rfl⟩
    · intro h; rcases h with ⟨y', hy', heq⟩ | ⟨y', hy', heq⟩
      · have hb := (Prod.mk.inj heq).1; have hy := (Prod.mk.inj heq).2
        subst hb; subst hy; exact hy'
      · have hb := (Prod.mk.inj heq).1; have hy := (Prod.mk.inj heq).2
        subst hb; subst hy; exact hy'
  rw [h2, Finset.card_union_of_disjoint h_disj, Finset.card_map, Finset.card_map]


lemma flipCoord_cons_zero {n : ℕ} (b : Bool) (y : Fin n → Bool) :
    flipCoord (Fin.cons b y : Fin (n+1) → Bool) 0 =
      (Fin.cons (!b) y : Fin (n+1) → Bool) := by
  unfold flipCoord
  simp only [Fin.cons_zero]
  ext j; cases j using Fin.cases with
  | zero => simp [Fin.cons_zero]
  | succ k => simp [Fin.succ_ne_zero, Fin.cons_succ]


lemma flipCoord_cons_succ {n : ℕ} (b : Bool) (y : Fin n → Bool) (i : Fin n) :
    flipCoord (Fin.cons b y : Fin (n+1) → Bool) (Fin.succ i) =
      (Fin.cons b (flipCoord y i) : Fin (n+1) → Bool) := by
  unfold flipCoord
  simp only [Fin.cons_succ]
  ext j; cases j using Fin.cases with
  | zero =>
    have h0 : (0 : Fin (n+1)) ≠ Fin.succ i := (Fin.succ_ne_zero i).symm
    simp [h0, Fin.cons_zero]
  | succ k =>
    simp only [Fin.cons_succ]
    by_cases h : k = i
    · subst h; simp
    · have hne : k.succ ≠ i.succ := fun h' => h (Fin.succ_injective _ h')
      simp [hne, h]


lemma influence_succ_eq {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) (i : Fin n) :
    influence f (Fin.succ i) =
    (influence (restrict f false) i + influence (restrict f true) i) / 2 := by
  unfold influence restrict

  have h_split := filter_card_split_by_first_coord
    (fun x => f x ≠ f (flipCoord x (Fin.succ i)))

  have h_false : (Finset.univ.filter fun y : Fin n → Bool =>
      f (Fin.cons false y) ≠ f (flipCoord (Fin.cons false y : Fin (n+1) → Bool) (Fin.succ i))) =
      (Finset.univ.filter fun y : Fin n → Bool =>
        f (Fin.cons false y) ≠ f (Fin.cons false (flipCoord y i))) := by
    congr 1; ext y; simp [flipCoord_cons_succ]
  have h_true : (Finset.univ.filter fun y : Fin n → Bool =>
      f (Fin.cons true y) ≠ f (flipCoord (Fin.cons true y : Fin (n+1) → Bool) (Fin.succ i))) =
      (Finset.univ.filter fun y : Fin n → Bool =>
        f (Fin.cons true y) ≠ f (Fin.cons true (flipCoord y i))) := by
    congr 1; ext y; simp [flipCoord_cons_succ]
  have h_card : ((Finset.univ.filter fun x : Fin (n+1) → Bool =>
      f x ≠ f (flipCoord x (Fin.succ i))).card : ℝ) =
    ((Finset.univ.filter fun y : Fin n → Bool =>
        f (Fin.cons false y) ≠ f (Fin.cons false (flipCoord y i))).card : ℝ) +
    ((Finset.univ.filter fun y : Fin n → Bool =>
        f (Fin.cons true y) ≠ f (Fin.cons true (flipCoord y i))).card : ℝ) := by
    have := h_split
    rw [h_false, h_true] at this
    exact_mod_cast this

  rw [show (2:ℝ) ^ (n + 1) = 2 * (2:ℝ) ^ n from by ring]
  field_simp
  linarith [h_card]


lemma card_disagree_ge_abs_diff {α : Type*} [Fintype α] [DecidableEq α]
    (f₀ f₁ : α → Bool) :
    ((Finset.univ.filter fun y => f₀ y ≠ f₁ y).card : ℝ) ≥
    |((Finset.univ.filter fun y => f₁ y = true).card : ℝ) -
     ((Finset.univ.filter fun y => f₀ y = true).card : ℝ)| := by
  set T₀ := Finset.univ.filter fun y => f₀ y = true
  set T₁ := Finset.univ.filter fun y => f₁ y = true
  set D := Finset.univ.filter fun y => f₀ y ≠ f₁ y
  have hT₁_sub : T₁ \ T₀ ⊆ D := by
    intro y hy
    simp only [T₁, T₀, D, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨h1, h2⟩ := hy
    intro heq; exact h2 (heq ▸ h1)
  have hT₀_sub : T₀ \ T₁ ⊆ D := by
    intro y hy
    simp only [T₁, T₀, D, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨h1, h2⟩ := hy
    intro heq; exact h2 (heq ▸ h1)
  have h_card_sdiff₁ : ((T₁ \ T₀).card : ℝ) ≤ (D.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card hT₁_sub)
  have h_card_sdiff₀ : ((T₀ \ T₁).card : ℝ) ≤ (D.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card hT₀_sub)
  have h_split₁ : (T₁.card : ℝ) = ((T₁ ∩ T₀).card : ℝ) + ((T₁ \ T₀).card : ℝ) := by
    push_cast [← Finset.card_sdiff_add_card_inter T₁ T₀]; ring
  have h_split₀ : (T₀.card : ℝ) = ((T₀ ∩ T₁).card : ℝ) + ((T₀ \ T₁).card : ℝ) := by
    push_cast [← Finset.card_sdiff_add_card_inter T₀ T₁]; ring
  have h_inter₁ : ((T₀ ∩ T₁).card : ℝ) ≤ (T₁.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)
  have h_inter₀ : ((T₁ ∩ T₀).card : ℝ) ≤ (T₀.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)
  rw [ge_iff_le, abs_le]
  constructor <;> linarith


lemma influence_zero_ge_abs_vol_diff {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) :
    influence f 0 ≥ |vol (restrict f true) - vol (restrict f false)| := by
  unfold influence vol restrict


  have h_split := filter_card_split_by_first_coord
    (fun x => f x ≠ f (flipCoord x 0))
  have h_false_filter : (Finset.univ.filter fun y : Fin n → Bool =>
      f (Fin.cons false y) ≠ f (flipCoord (Fin.cons false y : Fin (n+1) → Bool) 0)) =
      (Finset.univ.filter fun y : Fin n → Bool =>
        f (Fin.cons false y) ≠ f (Fin.cons true y)) := by
    congr 1; ext y; simp [flipCoord_cons_zero]
  have h_true_filter : (Finset.univ.filter fun y : Fin n → Bool =>
      f (Fin.cons true y) ≠ f (flipCoord (Fin.cons true y : Fin (n+1) → Bool) 0)) =
      (Finset.univ.filter fun y : Fin n → Bool =>
        f (Fin.cons true y) ≠ f (Fin.cons false y)) := by
    congr 1; ext y; simp [flipCoord_cons_zero]
  have h_ne_comm : (Finset.univ.filter fun y : Fin n → Bool =>
      f (Fin.cons true y) ≠ f (Fin.cons false y)) =
      (Finset.univ.filter fun y : Fin n → Bool =>
        f (Fin.cons false y) ≠ f (Fin.cons true y)) := by
    congr 1; ext y; exact ne_comm
  set Dis := (Finset.univ.filter fun y : Fin n → Bool =>
      f (Fin.cons false y) ≠ f (Fin.cons true y)).card
  have h_card_eq : (Finset.univ.filter fun x : Fin (n+1) → Bool =>
      f x ≠ f (flipCoord x 0)).card = 2 * Dis := by
    rw [h_split, h_false_filter, h_true_filter, h_ne_comm]
    ring


  have h_disagree := card_disagree_ge_abs_diff
    (fun y => f (Fin.cons false y)) (fun y => f (Fin.cons true y))

  have h_dis_eq : ((Finset.univ.filter fun y : Fin n → Bool =>
      (fun y => f (Fin.cons false y)) y ≠ (fun y => f (Fin.cons true y)) y).card : ℝ) =
      (Dis : ℝ) := by rfl
  rw [show (2:ℝ) ^ (n + 1) = 2 * (2:ℝ) ^ n from by ring]
  rw [show ∀ (a b : ℝ) (c : ℝ), a / c - b / c = (a - b) / c from fun a b c => by ring]
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 ^ n)]
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  have h_dis_val : (Dis : ℝ) ≥ |((Finset.univ.filter fun y : Fin n → Bool =>
      f (Fin.cons true y) = true).card : ℝ) -
     ((Finset.univ.filter fun y : Fin n → Bool =>
      f (Fin.cons false y) = true).card : ℝ)| := h_dis_eq ▸ h_disagree
  push_cast [h_card_eq]
  have : 2 * (Dis : ℝ) / (2 * 2 ^ n) = (Dis : ℝ) / 2 ^ n := by ring
  rw [this]
  exact div_le_div_of_nonneg_right h_dis_val h2n.le


theorem totalInfluence_restrict_bound {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) :
    totalInfluence f ≥
      (totalInfluence (restrict f false) + totalInfluence (restrict f true)) / 2 +
      |vol (restrict f true) - vol (restrict f false)| := by
  unfold totalInfluence
  rw [show (∑ i : Fin (n+1), influence f i) =
      influence f 0 + ∑ i : Fin n, influence f (Fin.succ i) from Fin.sum_univ_succ _]
  have h_succ : ∑ i : Fin n, influence f (Fin.succ i) =
      (∑ i : Fin n, influence (restrict f false) i +
       ∑ i : Fin n, influence (restrict f true) i) / 2 := by
    rw [show (∑ i : Fin n, influence (restrict f false) i +
       ∑ i : Fin n, influence (restrict f true) i) / 2 =
       ∑ i : Fin n, (influence (restrict f false) i + influence (restrict f true) i) / 2 from by
      rw [← Finset.sum_div, ← Finset.sum_add_distrib]]
    exact Finset.sum_congr rfl (fun i _ => influence_succ_eq f i)
  linarith [influence_zero_ge_abs_vol_diff f]

theorem tensorization_half (α₀ α₁ : ℝ)
    (hα₀_pos : 0 < α₀) (hα₁_pos : 0 < α₁)
    (hα₀_le : α₀ ≤ 1) (hα₁_le : α₁ ≤ 1) :
    (α₀ * (Real.log (1 / α₀) / Real.log 2) +
     α₁ * (Real.log (1 / α₁) / Real.log 2)) / 2 + |α₁ - α₀| ≥
    ((α₀ + α₁) / 2) * (Real.log (1 / ((α₀ + α₁) / 2)) / Real.log 2) := by
  have hlog2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have heq₀ : α₀ * (Real.log (1 / α₀) / Real.log 2) = negMulLog α₀ / Real.log 2 := by
    unfold negMulLog; rw [show (1:ℝ)/α₀ = α₀⁻¹ from one_div α₀, Real.log_inv]; ring
  have heq₁ : α₁ * (Real.log (1 / α₁) / Real.log 2) = negMulLog α₁ / Real.log 2 := by
    unfold negMulLog; rw [show (1:ℝ)/α₁ = α₁⁻¹ from one_div α₁, Real.log_inv]; ring
  have heqs : ((α₀ + α₁) / 2) * (Real.log (1 / ((α₀ + α₁) / 2)) / Real.log 2) =
      negMulLog ((α₀ + α₁) / 2) / Real.log 2 := by
    unfold negMulLog
    rw [show (1:ℝ)/((α₀ + α₁) / 2) = ((α₀ + α₁) / 2)⁻¹ from one_div _, Real.log_inv]; ring
  rw [heq₀, heq₁, heqs]
  suffices h_core : (negMulLog α₀ + negMulLog α₁) / 2 + |α₁ - α₀| * Real.log 2 ≥
      negMulLog ((α₀ + α₁) / 2) by
    have h3 := div_le_div_of_nonneg_right (show negMulLog ((α₀ + α₁) / 2) ≤
      (negMulLog α₀ + negMulLog α₁) / 2 + |α₁ - α₀| * Real.log 2 from h_core) hlog2_pos.le
    have h4 : ((negMulLog α₀ + negMulLog α₁) / 2 + |α₁ - α₀| * Real.log 2) / Real.log 2 =
        (negMulLog α₀ / Real.log 2 + negMulLog α₁ / Real.log 2) / 2 + |α₁ - α₀| := by
      field_simp
    linarith
  set C := α₀ + α₁
  have hC_pos : 0 < C := by linarith
  have hC_le : C ≤ 2 := by linarith
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  set p := α₀ / C
  have hp_pos : 0 < p := div_pos hα₀_pos hC_pos
  have hp_lt1 : p < 1 := by rw [div_lt_one hC_pos]; linarith
  have hpC_eq : p * C = α₀ := div_mul_cancel₀ α₀ hC_ne
  have h1mpC_eq : (1 - p) * C = α₁ := by
    have : α₁ = C - α₀ := by linarith
    rw [this, ← hpC_eq]; ring
  have habs_eq : |(1 - p) * C - p * C| = |1 - 2 * p| * C := by
    rw [show (1 - p) * C - p * C = (1 - 2 * p) * C from by ring, abs_mul, abs_of_pos hC_pos]
  have h_lhs : (negMulLog (p * C) + negMulLog ((1-p) * C)) / 2 =
      C / 2 * (binEntropy p + Real.log (1/C)) := by
    simp only [negMulLog, binEntropy]
    rw [Real.log_mul (ne_of_gt hp_pos) hC_ne,
        Real.log_mul (ne_of_gt (show 0 < 1-p by linarith)) hC_ne]
    rw [show (1 : ℝ) / C = C⁻¹ from one_div C, Real.log_inv, Real.log_inv, Real.log_inv]
    ring
  have h_rhs : negMulLog (C / 2) = (C / 2) * (Real.log 2 + Real.log (1 / C)) := by
    simp only [negMulLog]
    rw [Real.log_div hC_ne (show (2:ℝ) ≠ 0 from by norm_num)]
    rw [show (1:ℝ)/C = C⁻¹ from one_div C, Real.log_inv]
    ring
  rw [← hpC_eq, ← h1mpC_eq, h_lhs, habs_eq, h_rhs]
  suffices h : binEntropy p + (2*|1 - 2*p| - 1) * Real.log 2 ≥ 0 by
    have hlog1C : Real.log (1/C) ≥ -Real.log 2 := by
      rw [show (1:ℝ)/C = C⁻¹ from one_div C, Real.log_inv]
      linarith [Real.log_le_log hC_pos hC_le]
    nlinarith [hC_pos, hlog1C]
  have habs_nn : (0:ℝ) ≤ |1 - 2*p| := abs_nonneg _
  suffices h_weak : binEntropy p + (|1 - 2*p| - 1) * Real.log 2 ≥ 0 by
    nlinarith [hlog2_pos]
  rcases le_or_gt p (1/2) with hp_le | hp_gt
  · have h_abs : |1 - 2*p| = 1 - 2*p := abs_of_nonneg (by linarith)
    rw [h_abs, show (1 - 2*p - 1) = -(2*p) from by ring]
    have hcc := strictConcave_binEntropy.concaveOn
    have hcomb : (1 - 2*p) • (0 : ℝ) + (2*p) • (2⁻¹ : ℝ) = p := by simp [smul_eq_mul]; ring
    have hineq := hcc.2 (show (0:ℝ) ∈ Set.Icc 0 1 from ⟨le_refl _, zero_le_one⟩)
      (show (2⁻¹:ℝ) ∈ Set.Icc 0 1 from ⟨by norm_num, by norm_num⟩)
      (show (0:ℝ) ≤ 1 - 2*p from by linarith) (show (0:ℝ) ≤ 2*p from by linarith)
      (show (1 - 2*p) + 2*p = 1 from by ring)
    rw [hcomb] at hineq
    simp only [binEntropy_zero, smul_eq_mul, mul_zero, zero_add, binEntropy_two_inv] at hineq
    linarith
  · have h_abs : |1 - 2*p| = -(1 - 2*p) := abs_of_nonpos (by linarith)
    rw [h_abs, show -(1 - 2 * p) - 1 = -(2*(1-p)) from by ring]
    have h_sym : binEntropy p = binEntropy (1 - p) := by rw [binEntropy_one_sub]
    rw [h_sym]
    have hcc := strictConcave_binEntropy.concaveOn
    have hcomb : (1 - 2*(1-p)) • (0 : ℝ) + (2*(1-p)) • (2⁻¹ : ℝ) = 1-p := by
      simp [smul_eq_mul]; ring
    have hineq := hcc.2 (show (0:ℝ) ∈ Set.Icc 0 1 from ⟨le_refl _, zero_le_one⟩)
      (show (2⁻¹:ℝ) ∈ Set.Icc 0 1 from ⟨by norm_num, by norm_num⟩)
      (show (0:ℝ) ≤ 1 - 2*(1-p) from by linarith) (show (0:ℝ) ≤ 2*(1-p) from by linarith)
      (show (1 - 2*(1-p)) + 2*(1-p) = 1 from by ring)
    rw [hcomb] at hineq
    simp only [binEntropy_zero, smul_eq_mul, mul_zero, zero_add, binEntropy_two_inv] at hineq
    linarith

lemma tensorization_half_boundary_left (α₁ : ℝ)
    (hα₁_pos : 0 < α₁) (hα₁_le : α₁ ≤ 1) :
    (0 * (Real.log (1 / (0:ℝ)) / Real.log 2) +
     α₁ * (Real.log (1 / α₁) / Real.log 2)) / 2 + |α₁ - 0| ≥
    ((0 + α₁) / 2) * (Real.log (1 / ((0 + α₁) / 2)) / Real.log 2) := by
  simp only [zero_mul, zero_add, sub_zero, abs_of_pos hα₁_pos]
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [show (1:ℝ) / (α₁ / 2) = 2 / α₁ from by ring]
  rw [show (2:ℝ) / α₁ = 2 * (1/α₁) from by ring,
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : (1:ℝ)/α₁ ≠ 0)]
  have : α₁ / 2 * ((Real.log 2 + Real.log (1 / α₁)) / Real.log 2) =
      α₁ / 2 + α₁ / 2 * (Real.log (1 / α₁) / Real.log 2) := by field_simp
  linarith

lemma tensorization_half_boundary_right (α₀ : ℝ)
    (hα₀_pos : 0 < α₀) (hα₀_le : α₀ ≤ 1) :
    (α₀ * (Real.log (1 / α₀) / Real.log 2) +
     0 * (Real.log (1 / (0:ℝ)) / Real.log 2)) / 2 + |0 - α₀| ≥
    ((α₀ + 0) / 2) * (Real.log (1 / ((α₀ + 0) / 2)) / Real.log 2) := by
  simp only [zero_mul, add_zero, show (0:ℝ) - α₀ = -α₀ from by ring, abs_neg, abs_of_pos hα₀_pos]
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [show (1:ℝ) / (α₀ / 2) = 2 / α₀ from by ring]
  rw [show (2:ℝ) / α₀ = 2 * (1/α₀) from by ring,
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : (1:ℝ)/α₀ ≠ 0)]
  have : α₀ / 2 * ((Real.log 2 + Real.log (1 / α₀)) / Real.log 2) =
      α₀ / 2 + α₀ / 2 * (Real.log (1 / α₀) / Real.log 2) := by field_simp
  linarith


theorem totalInfluence_ge_two_vol_log
    {n : ℕ} (f : (Fin n → Bool) → Bool) :
    totalInfluence f ≥
      (1 - vol f) * (Real.log (1 / (1 - vol f)) / Real.log 2) := by
  induction n with
  | zero =>

    have h_ti : totalInfluence f = 0 := by
      unfold totalInfluence; simp
    rw [h_ti]
    suffices h : (1 - vol f) * (Real.log (1 / (1 - vol f)) / Real.log 2) = 0 by linarith
    have h_vol : vol f = 0 ∨ vol f = 1 := by
      unfold vol
      simp only [pow_zero, div_one]
      set c := (Finset.univ.filter fun x : Fin 0 → Bool => f x = true).card
      have hc_le : c ≤ 1 := by
        calc c ≤ (Finset.univ : Finset (Fin 0 → Bool)).card := Finset.card_filter_le _ _
          _ = Fintype.card (Fin 0 → Bool) := rfl
          _ = 1 := by simp
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc_le with h0 | h1
      · left; simp [h0]
      · right; simp [h1]
    rcases h_vol with hv | hv
    · rw [hv]; simp [Real.log_one]
    · rw [hv]; simp
  | succ m ih =>

    set α₀ := 1 - vol (restrict f false)
    set α₁ := 1 - vol (restrict f true)
    set α := 1 - vol f

    have hα₀_nn : 0 ≤ α₀ := by show 0 ≤ 1 - vol (restrict f false); linarith [vol_le_one (restrict f false)]
    have hα₁_nn : 0 ≤ α₁ := by show 0 ≤ 1 - vol (restrict f true); linarith [vol_le_one (restrict f true)]
    have hα₀_le : α₀ ≤ 1 := by show 1 - vol (restrict f false) ≤ 1; linarith [vol_nonneg (restrict f false)]
    have hα₁_le : α₁ ≤ 1 := by show 1 - vol (restrict f true) ≤ 1; linarith [vol_nonneg (restrict f true)]

    have hα_eq : α = (α₀ + α₁) / 2 := by
      show 1 - vol f = (1 - vol (restrict f false) + (1 - vol (restrict f true))) / 2
      have := vol_restrict_decomp f
      linarith

    have ih₀ := ih (restrict f false)
    have ih₁ := ih (restrict f true)

    have h_bound := totalInfluence_restrict_bound f

    have h_abs_eq : |vol (restrict f true) - vol (restrict f false)| = |α₁ - α₀| := by
      show |vol (restrict f true) - vol (restrict f false)| =
        |(1 - vol (restrict f true)) - (1 - vol (restrict f false))|
      rw [show (1 - vol (restrict f true)) - (1 - vol (restrict f false)) =
        -(vol (restrict f true) - vol (restrict f false)) from by ring, abs_neg]

    have h_combined : totalInfluence f ≥
        (α₀ * (Real.log (1 / α₀) / Real.log 2) +
         α₁ * (Real.log (1 / α₁) / Real.log 2)) / 2 + |α₁ - α₀| := by
      rw [show α₀ = 1 - vol (restrict f false) from rfl,
          show α₁ = 1 - vol (restrict f true) from rfl,
          show |α₁ - α₀| = |vol (restrict f true) - vol (restrict f false)| from by
            show |(1 - vol (restrict f true)) - (1 - vol (restrict f false))| =
              |vol (restrict f true) - vol (restrict f false)|
            rw [show (1 - vol (restrict f true)) - (1 - vol (restrict f false)) =
              -(vol (restrict f true) - vol (restrict f false)) from by ring, abs_neg]]
      linarith


    have h_tensor : (α₀ * (Real.log (1 / α₀) / Real.log 2) +
         α₁ * (Real.log (1 / α₁) / Real.log 2)) / 2 + |α₁ - α₀| ≥
        α * (Real.log (1 / α) / Real.log 2) := by
      rw [hα_eq]
      rcases eq_or_lt_of_le hα₀_nn with (hα₀_zero | hα₀_pos)
      · rcases eq_or_lt_of_le hα₁_nn with (hα₁_zero | hα₁_pos)
        ·
          rw [← hα₀_zero, ← hα₁_zero]; simp
        ·
          rw [← hα₀_zero]
          exact tensorization_half_boundary_left α₁ hα₁_pos hα₁_le
      · rcases eq_or_lt_of_le hα₁_nn with (hα₁_zero | hα₁_pos)
        ·
          rw [← hα₁_zero]
          exact tensorization_half_boundary_right α₀ hα₀_pos hα₀_le
        ·
          exact tensorization_half α₀ α₁ hα₀_pos hα₁_pos hα₀_le hα₁_le
    linarith

end BooleanFourier
