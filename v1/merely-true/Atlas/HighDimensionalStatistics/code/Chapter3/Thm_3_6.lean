/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter3.Remark_3_1
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option maxHeartbeats 6400000

open Matrix Finset BigOperators

namespace Chapter3

/-- Distributive factorization of a sum of products over functions
`Fin k → S` into a product of sums. -/
lemma prod_dist_factorize {S : Type} [Fintype S] [DecidableEq S] {k : ℕ}
    (h : Fin k → S → ℝ) :
    ∑ sel : Fin k → S, ∏ l, h l (sel l) = ∏ l, ∑ j, h l j := by
  have := (Finset.prod_univ_sum (t := fun _ : Fin k => (Finset.univ : Finset S))
    (f := fun l j => h l j)).symm
  rwa [Fintype.piFinset_univ] at this

/-- The product weights `∏_l w(sel_l)` sum to `1` over all selections
`sel : Fin k → S` when `w` itself sums to `1`. -/
lemma product_weight_sum {S : Type} [Fintype S] [DecidableEq S] {k : ℕ}
    (w : S → ℝ) (hw_sum : ∑ j, w j = 1) :
    ∑ sel : Fin k → S, ∏ l, w (sel l) = 1 := by
  rw [show ∑ sel : Fin k → S, ∏ l, w (sel l) =
    ∑ sel ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset S)), ∏ l, w (sel l) from by
    rw [Fintype.piFinset_univ]]
  rw [← Finset.prod_univ_sum (t := fun _ => Finset.univ) (f := fun _ j => w j)]
  simp only [Finset.prod_const, Finset.card_fin, hw_sum, one_pow]

/-- One-dimensional marginal of the product weighting: weighting a function
`f(sel_{l₀})` of a single coordinate by the product `∏_l w(sel_l)` yields
the simple weighted sum `∑ⱼ w(j) f(j)`. -/
lemma product_marginal {S : Type} [Fintype S] [DecidableEq S]
    {k : ℕ} (w : S → ℝ) (hw_sum : ∑ j, w j = 1)
    (f : S → ℝ) (l₀ : Fin k) :
    ∑ sel : Fin k → S, (∏ l, w (sel l)) * f (sel l₀) =
    ∑ j, w j * f j := by
  let h : Fin k → S → ℝ := fun l j => if l = l₀ then w j * f j else w j
  have step1 : ∀ sel : Fin k → S,
    (∏ l, w (sel l)) * f (sel l₀) = ∏ l, h l (sel l) := by
    intro sel; simp only [h]
    have h1 : ∏ l : Fin k, (if l = l₀ then w (sel l) * f (sel l) else w (sel l)) =
      (w (sel l₀) * f (sel l₀)) * ∏ l ∈ Finset.univ.erase l₀, w (sel l) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l₀)]; simp only [ite_true]; congr 1
      apply Finset.prod_congr rfl; intro l hl
      rw [Finset.mem_erase] at hl; simp [hl.1]
    rw [h1, ← Finset.mul_prod_erase _ (fun l => w (sel l)) (Finset.mem_univ l₀)]; ring
  simp_rw [step1, prod_dist_factorize]; simp only [h]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l₀)]
  simp only [ite_true]
  have : ∀ l ∈ Finset.univ.erase l₀, (∑ j : S, if l = l₀ then w j * f j else w j) = ∑ j, w j := by
    intro l hl; rw [Finset.mem_erase] at hl; simp [hl.1]
  rw [Finset.prod_congr rfl this, hw_sum, Finset.prod_const_one, mul_one]

/-- Two-dimensional marginal: for distinct coordinates `l₁ ≠ l₂`, the
product weighting factorizes into independent expectations. -/
lemma product_cross_marginal {S : Type} [Fintype S] [DecidableEq S]
    {k : ℕ} (w : S → ℝ) (hw_sum : ∑ j, w j = 1)
    (f g : S → ℝ) (l₁ l₂ : Fin k) (hne : l₁ ≠ l₂) :
    ∑ sel : Fin k → S, (∏ l, w (sel l)) * (f (sel l₁) * g (sel l₂)) =
    (∑ j, w j * f j) * (∑ j, w j * g j) := by
  let h : Fin k → S → ℝ := fun l j =>
    if l = l₁ then w j * f j else if l = l₂ then w j * g j else w j
  have step1 : ∀ sel : Fin k → S,
    (∏ l, w (sel l)) * (f (sel l₁) * g (sel l₂)) = ∏ l, h l (sel l) := by
    intro sel; simp only [h]
    have hRHS : ∏ l : Fin k, (if l = l₁ then w (sel l) * f (sel l)
        else if l = l₂ then w (sel l) * g (sel l) else w (sel l))
      = (w (sel l₁) * f (sel l₁)) * ((w (sel l₂) * g (sel l₂)) *
        ∏ l ∈ (Finset.univ.erase l₁).erase l₂, w (sel l)) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l₁)]
      congr 1; · simp
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ l₂⟩)]
      congr 1; · have : l₂ ≠ l₁ := hne.symm; simp [this]
      apply Finset.prod_congr rfl; intro l hl; rw [Finset.mem_erase] at hl
      have hl2 := hl.1; have hl1 := (Finset.mem_erase.mp hl.2).1; simp [hl1, hl2]
    rw [hRHS, ← Finset.mul_prod_erase Finset.univ (fun l => w (sel l)) (Finset.mem_univ l₁)]
    rw [← Finset.mul_prod_erase _ (fun l => w (sel l)) (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ l₂⟩)]
    ring
  simp_rw [step1, prod_dist_factorize]; simp only [h]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l₁)]
  simp only [ite_true]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ l₂⟩)]
  have hne' : l₂ ≠ l₁ := hne.symm
  simp only [hne', ite_false, ite_true]
  have : ∀ l ∈ (Finset.univ.erase l₁).erase l₂,
    ∑ j : S, (if l = l₁ then w j * f j else if l = l₂ then w j * g j else w j) = ∑ j, w j := by
    intro l hl; rw [Finset.mem_erase] at hl
    have hl2 := hl.1; have hl1 := (Finset.mem_erase.mp hl.2).1; simp [hl1, hl2]
  rw [Finset.prod_congr rfl this, hw_sum, Finset.prod_const_one, mul_one]

/-- Bias-variance decomposition for the squared sum of `k` i.i.d. draws
under product weighting: the expected `(∑_l a(sel_l))²` equals
`k · 𝔼[a²] + k(k-1) · (𝔼 a)²`. -/
lemma expected_sum_sq {S : Type} [Fintype S] [DecidableEq S]
    {k : ℕ} (hk : 1 ≤ k) (w : S → ℝ) (hw_sum : ∑ j, w j = 1) (a : S → ℝ) :
    ∑ sel : Fin k → S, (∏ l, w (sel l)) * (∑ l, a (sel l)) ^ 2 =
    ↑k * (∑ j, w j * a j ^ 2) + ↑k * (↑k - 1) * (∑ j, w j * a j) ^ 2 := by
  have h1 : ∀ sel : Fin k → S, (∏ l, w (sel l)) * (∑ l, a (sel l)) ^ 2 =
    ∑ l₁ : Fin k, ∑ l₂ : Fin k, (∏ l, w (sel l)) * (a (sel l₁) * a (sel l₂)) := by
    intro sel; rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    congr 1; ext l₁; rw [Finset.mul_sum]
  simp_rw [h1]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin k → S))]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := Fin k → S))]
  have h3 : ∀ l₁ : Fin k, ∑ l₂ : Fin k,
    ∑ sel : Fin k → S, (∏ l, w (sel l)) * (a (sel l₁) * a (sel l₂)) =
    (∑ j, w j * a j ^ 2) + ∑ l₂ ∈ Finset.univ.erase l₁,
      ∑ sel : Fin k → S, (∏ l, w (sel l)) * (a (sel l₁) * a (sel l₂)) := by
    intro l₁; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l₁)]; congr 1
    convert product_marginal w hw_sum (fun j => a j ^ 2) l₁ using 1
    congr 1; ext sel; congr 1; ring
  simp_rw [h3, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  · have h4 : ∀ (l₁ l₂ : Fin k), l₁ ≠ l₂ →
      ∑ sel : Fin k → S, (∏ l, w (sel l)) * (a (sel l₁) * a (sel l₂)) =
      (∑ j, w j * a j) ^ 2 := by
      intro l₁ l₂ hne; rw [sq, product_cross_marginal w hw_sum a a l₁ l₂ hne]
    have h5 : ∀ l₁ : Fin k, ∑ l₂ ∈ Finset.univ.erase l₁,
      ∑ sel : Fin k → S, (∏ l, w (sel l)) * (a (sel l₁) * a (sel l₂)) =
      (↑k - 1) * (∑ j, w j * a j) ^ 2 := by
      intro l₁
      have h6 : ∀ l₂ ∈ Finset.univ.erase l₁,
        ∑ sel : Fin k → S, (∏ l, w (sel l)) * (a (sel l₁) * a (sel l₂)) =
        (∑ j, w j * a j) ^ 2 := by
        intro l₂ hl₂; exact h4 l₁ l₂ (Finset.ne_of_mem_erase hl₂).symm
      rw [Finset.sum_congr rfl h6, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin, nsmul_eq_mul]
      congr 1
      have := @Nat.cast_sub ℝ _ 1 k hk; simp only [Nat.cast_one] at this; linarith
    simp_rw [h5, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring

/-- Probabilistic existence principle: if the weighted average of `f` is at
most `c`, then some index achieves `f(i) ≤ c`. -/
lemma exists_le_of_weighted_sum {ι : Type*} [Fintype ι] (w : ι → ℝ) (f : ι → ℝ) (c : ℝ)
    (hw_nn : ∀ i, 0 ≤ w i) (hw_pos : 0 < ∑ i, w i)
    (havg : ∑ i, w i * f i ≤ (∑ i, w i) * c) :
    ∃ i, f i ≤ c := by
  by_contra h
  push_neg at h
  have hge : ∀ i, w i * c ≤ w i * f i := fun i =>
    mul_le_mul_of_nonneg_left (h i).le (hw_nn i)
  obtain ⟨j, _, hwj_pos⟩ : ∃ j ∈ Finset.univ, 0 < w j := by
    by_contra hall
    push_neg at hall
    have : ∑ i, w i ≤ 0 := Finset.sum_nonpos (fun i hi =>
      le_antisymm (hall i hi) (hw_nn i) ▸ le_refl _)
    linarith
  have hstrict : w j * c < w j * f j := mul_lt_mul_of_pos_left (h j) hwj_pos
  have : (∑ i, w i) * c < ∑ i, w i * f i := by
    have hh : ∑ i : ι, w i * c < ∑ i : ι, w i * f i :=
      Finset.sum_lt_sum (fun i _ => hge i) ⟨j, Finset.mem_univ j, hstrict⟩
    rwa [← Finset.sum_mul] at hh
  linarith

/-- Existence step in Maurey's empirical method: there exists a selection
`sel : Fin k → S` such that the empirical mean of `u(sel_l)` approximates
`g` with error controlled by the population mean plus a `B / k` term. -/
theorem product_averaging_existence
    {n : ℕ} (S : Type) [Fintype S] [Nonempty S]
    (w : S → ℝ) (hw_nn : ∀ j, 0 ≤ w j) (hw_sum : ∑ j, w j = 1)
    (u : S → (Fin n → ℝ)) (g : Fin n → ℝ)
    (B : ℝ) (hB : ∀ j, ∑ i, (u j i) ^ 2 ≤ B)
    (k : ℕ) (hk : 1 ≤ k) :
    let μ := fun i => ∑ j, w j * u j i
    ∃ (sel : Fin k → S),
      ∑ i, (g i - (1 / ↑k) * ∑ l, u (sel l) i) ^ 2 ≤
        ∑ i, (g i - μ i) ^ 2 + B / ↑k := by
  classical
  intro μ
  let W : (Fin k → S) → ℝ := fun sel => ∏ l, w (sel l)
  let err : (Fin k → S) → ℝ := fun sel =>
    ∑ i, (g i - (1 / ↑k) * ∑ l, u (sel l) i) ^ 2
  let target := ∑ i, (g i - μ i) ^ 2 + B / ↑k
  have hW_nn : ∀ sel, 0 ≤ W sel := fun sel =>
    Finset.prod_nonneg (fun l _ => hw_nn (sel l))
  have hW_sum : ∑ sel, W sel = 1 := product_weight_sum w hw_sum
  have hW_pos : 0 < ∑ sel : Fin k → S, W sel := by rw [hW_sum]; exact one_pos
  have hk_pos : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (by omega)
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos

  suffices havg : ∑ sel, W sel * err sel ≤ (∑ sel, W sel) * target by
    exact exists_le_of_weighted_sum W err target hW_nn hW_pos havg
  rw [hW_sum, one_mul]

  have swap_eq : ∑ sel, W sel * err sel =
    ∑ i : Fin n, ∑ sel : Fin k → S, W sel * (g i - (1/↑k) * ∑ l, u (sel l) i) ^ 2 := by
    simp only [err, W, Finset.mul_sum]; rw [Finset.sum_comm]
  rw [swap_eq]
  have coord_eq : ∀ i : Fin n,
    ∑ sel : Fin k → S, W sel * (g i - (1/↑k) * ∑ l, u (sel l) i) ^ 2 =
    (g i - μ i) ^ 2 + ((∑ j, w j * (u j i) ^ 2) - (μ i) ^ 2) / ↑k := by
    intro i
    have expand : ∀ sel : Fin k → S,
      (g i - (1/↑k) * ∑ l, u (sel l) i) ^ 2 =
      (g i)^2 - 2 * (g i) * ((1/↑k) * ∑ l, u (sel l) i) +
      ((1/↑k) * ∑ l, u (sel l) i)^2 := by
      intro sel; ring
    simp_rw [expand]
    simp_rw [mul_add, mul_sub]
    have term_split : ∀ (a b c : (Fin k → S) → ℝ),
      ∑ sel, (a sel - b sel + c sel) = ∑ sel, a sel - ∑ sel, b sel + ∑ sel, c sel := by
      intro a b c; simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [term_split]
    have t1 : ∑ sel : Fin k → S, W sel * (g i) ^ 2 = (g i) ^ 2 := by
      rw [← Finset.sum_mul, hW_sum, one_mul]
    have t2 : ∑ sel : Fin k → S, W sel * (2 * g i * (1 / ↑k * ∑ l, u (sel l) i)) =
      2 * g i * μ i := by
      have h2a : ∀ sel : Fin k → S,
        W sel * (2 * g i * (1 / ↑k * ∑ l, u (sel l) i)) =
        (2 * g i / ↑k) * ∑ l, W sel * u (sel l) i := by
        intro sel; simp only [← Finset.mul_sum]; ring
      simp_rw [h2a]
      rw [← Finset.mul_sum, Finset.sum_comm (s := Finset.univ (α := Fin k → S))]
      have h2b : ∀ l : Fin k, ∑ sel : Fin k → S, W sel * u (sel l) i = μ i := by
        intro l; exact product_marginal w hw_sum (fun j => u j i) l
      simp_rw [h2b, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      field_simp
    have t3 : ∑ sel : Fin k → S, W sel * (1 / ↑k * ∑ l, u (sel l) i) ^ 2 =
      (∑ j, w j * (u j i) ^ 2) / ↑k + (↑k - 1) / ↑k * (μ i) ^ 2 := by
      have h3a : ∀ sel : Fin k → S,
        W sel * (1 / ↑k * ∑ l, u (sel l) i) ^ 2 =
        (1 / ↑k) ^ 2 * (W sel * (∑ l, u (sel l) i) ^ 2) := by
        intro sel; ring
      simp_rw [h3a, ← Finset.mul_sum]
      rw [expected_sum_sq hk w hw_sum (fun j => u j i)]
      field_simp; ring
    rw [t1, t2, t3]
    field_simp; ring
  simp_rw [coord_eq]
  rw [Finset.sum_add_distrib]
  have bound : ∑ i : Fin n, ((∑ j, w j * (u j i) ^ 2) - (μ i) ^ 2) / ↑k ≤ B / ↑k := by
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ hk_pos.le
    calc ∑ i, ((∑ j, w j * (u j i) ^ 2) - (μ i) ^ 2)
        ≤ ∑ i, (∑ j, w j * (u j i) ^ 2) := by
          apply Finset.sum_le_sum; intro i _
          linarith [sq_nonneg (μ i)]
      _ = ∑ j, w j * ∑ i, (u j i) ^ 2 := by
          rw [Finset.sum_comm]; congr 1; ext j
          rw [Finset.mul_sum]
      _ ≤ ∑ j, w j * B := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left (hB j) (hw_nn j)
      _ = B := by rw [← Finset.sum_mul, hw_sum, one_mul]
  linarith

/-- Maurey's sparse approximation lemma: any `θ` with `‖θ‖₁ ≤ R` can be
approximated by a `2k`-sparse vector `θ'` with
`MSE(Φ θ', f) ≤ MSE(Φ θ, f) + D² R² / k`, provided each column of `Φ` has
squared norm at most `D² n`. -/
theorem maurey_sparse_approx
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ) (f : Fin n → ℝ)
    (D : ℝ) (hD : 0 < D)
    (hNorm : ∀ j : Fin M, ∑ i : Fin n, (Φ i j) ^ 2 ≤ D ^ 2 * n)
    (k : ℕ) (hk : 1 ≤ k) (R : ℝ) (hR : 0 < R)
    (θ : Fin M → ℝ) (hθ : l1norm θ ≤ R) :
    ∃ θ' : Fin M → ℝ, support_size θ' ≤ 2 * k ∧
      MSE (Φ.mulVec θ') f ≤ MSE (Φ.mulVec θ) f + D ^ 2 * R ^ 2 / ↑k := by

  by_cases hR0 : l1norm θ = 0
  · refine ⟨0, ?_, ?_⟩
    · unfold support_size; simp
    · have h0 : ∀ j, θ j = 0 := by
        intro j
        have hle := Finset.single_le_sum (fun j _ => abs_nonneg (θ j)) (Finset.mem_univ j)
        simp only [l1norm] at hR0
        have : |θ j| = 0 := le_antisymm (by linarith) (abs_nonneg _)
        exact abs_eq_zero.mp this
      have : Φ.mulVec θ = Φ.mulVec 0 := by
        ext i; simp [Matrix.mulVec, dotProduct, h0]
      rw [this]
      linarith [div_nonneg (mul_nonneg (sq_nonneg D) (sq_nonneg R)) (Nat.cast_nonneg' k)]

  have hR_pos : 0 < l1norm θ := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => abs_nonneg (θ j))
    exact lt_of_le_of_ne this (Ne.symm hR0)

  let S := Option (Fin M)
  let sign : Fin M → ℝ := fun j => if 0 ≤ θ j then 1 else -1
  let w : S → ℝ := fun s => match s with
    | none => 1 - l1norm θ / R
    | some j => |θ j| / R
  let atom : S → (Fin n → ℝ) := fun s => match s with
    | none => fun _ => 0
    | some j => fun i => R * sign j * Φ i j

  have hw_nn : ∀ s : S, 0 ≤ w s := by
    intro s; cases s with
    | none =>
      simp only [w]
      have : l1norm θ / R ≤ 1 := (div_le_one₀ hR).mpr hθ
      linarith
    | some j =>
      simp only [w]
      exact div_nonneg (abs_nonneg _) hR.le

  have hw_sum : ∑ s : S, w s = 1 := by
    show ∑ s : Option (Fin M), (match s with | none => 1 - l1norm θ / R | some j => |θ j| / R) = 1
    rw [Fintype.sum_option]
    simp only []
    have : ∑ j : Fin M, |θ j| / R = l1norm θ / R := by
      simp only [l1norm]; exact (Finset.sum_div (Finset.univ) (fun j => |θ j|) R).symm
    linarith

  have hB : ∀ s : S, ∑ i : Fin n, (atom s i) ^ 2 ≤ D ^ 2 * R ^ 2 * ↑n := by
    intro s; cases s with
    | none =>
      simp only [atom]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
      positivity
    | some j =>
      simp only [atom]
      calc ∑ i, (R * sign j * Φ i j) ^ 2
          = ∑ i, R ^ 2 * (Φ i j) ^ 2 := by
            congr 1; ext i; simp only [sign]; split_ifs <;> ring
        _ = R ^ 2 * ∑ i, (Φ i j) ^ 2 := (Finset.mul_sum ..).symm
        _ ≤ R ^ 2 * (D ^ 2 * ↑n) :=
            mul_le_mul_of_nonneg_left (hNorm j) (sq_nonneg R)
        _ = D ^ 2 * R ^ 2 * ↑n := by ring

  have h_mean : ∀ i : Fin n, (∑ s : S, w s * atom s i) = (Φ.mulVec θ) i := by
    intro i
    show ∑ s : Option (Fin M), (match s with | none => 1 - l1norm θ / R | some j => |θ j| / R) *
      (match s with | none => (fun _ => 0) | some j => (fun i => R * sign j * Φ i j)) i = _
    rw [Fintype.sum_option]
    dsimp only []
    simp only [mul_zero, zero_add, Matrix.mulVec, dotProduct]
    congr 1; ext j
    have hRne : R ≠ 0 := ne_of_gt hR
    simp only [sign]
    split_ifs with h
    · rw [abs_of_nonneg h]; field_simp
    · push_neg at h; rw [abs_of_neg h]; field_simp

  have hS_ne : Nonempty S := ⟨none⟩
  obtain ⟨sel, h_sel⟩ := product_averaging_existence S w hw_nn hw_sum atom f
    (D ^ 2 * R ^ 2 * ↑n) hB k hk

  let θ' : Fin M → ℝ := fun j =>
    (R * sign j / ↑k) *
      ↑((Finset.univ.filter (fun l : Fin k => sel l = some j)).card)
  refine ⟨θ', ?_, ?_⟩

  · unfold support_size
    have h_sub : (univ.filter fun j : Fin M => θ' j ≠ 0) ⊆
        (univ.filter fun j : Fin M => ∃ l : Fin k, sel l = some j) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_contra h_not
      push_neg at h_not
      have h_empty : (univ.filter fun l : Fin k => sel l = some j).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro l _; exact h_not l
      have : θ' j = 0 := by
        show (R * sign j / ↑k) * ↑(#{l | sel l = some j}) = 0
        simp [h_empty]
      exact hj this
    calc (univ.filter fun j => θ' j ≠ 0).card
        ≤ (univ.filter fun j : Fin M => ∃ l : Fin k, sel l = some j).card :=
          Finset.card_le_card h_sub
      _ ≤ ((univ : Finset (Fin k)).biUnion (fun l =>
            match sel l with | some j => {j} | none => ∅)).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
          obtain ⟨l, hl⟩ := hj
          exact ⟨l, by simp [hl]⟩
      _ ≤ ∑ l : Fin k, (match sel l with | some j => ({j} : Finset (Fin M)) | none => ∅).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _l : Fin k, 1 := by
          apply Finset.sum_le_sum; intro l _; cases h : sel l <;> simp
      _ = k := by simp
      _ ≤ 2 * k := le_mul_of_one_le_left (Nat.zero_le k) one_le_two

  · have h_mulvec : ∀ i : Fin n, (Φ.mulVec θ') i = (1 / ↑k) * ∑ l, atom (sel l) i := by
      intro i
      simp only [Matrix.mulVec, dotProduct]
      have h_lhs : ∀ j : Fin M, Φ i j * θ' j =
          Φ i j * ((R * sign j / ↑k) * ↑(#{l | sel l = some j})) := by
        intro j; rfl
      simp_rw [h_lhs]
      have h_fiber : ∑ l : Fin k, atom (sel l) i =
          ∑ j : Fin M, ↑(#{l : Fin k | sel l = some j}) * atom (some j) i := by
        conv_lhs => rw [show (∑ l : Fin k, atom (sel l) i) =
          ∑ s : Option (Fin M), ∑ x : { l // sel l = s }, atom (sel ↑x) i
          from (Fintype.sum_fiberwise sel (fun l => atom (sel l) i)).symm]
        rw [Fintype.sum_option]
        have h_none : (∑ x : { l // sel l = none }, atom (sel ↑x) i) = 0 := by
          apply Finset.sum_eq_zero; intro ⟨l, hl⟩ _; simp only [atom, hl, mul_zero]
        rw [h_none, zero_add]
        congr 1; ext j
        have : ∀ x : { l // sel l = some j }, atom (sel ↑x) i = atom (some j) i := by
          intro ⟨l, hl⟩; simp [hl]
        simp_rw [this, Finset.sum_const, nsmul_eq_mul]
        congr 1; rw [Finset.card_univ, Fintype.card_subtype]
      rw [h_fiber]
      simp only [atom]
      have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [one_div, inv_mul_eq_div, Finset.sum_div]
      congr 1; ext j; field_simp
    have h_sel_rewrite : ∑ i : Fin n, (f i - (1 / ↑k) * ∑ l, atom (sel l) i) ^ 2 ≤
        ∑ i : Fin n, (f i - (Φ.mulVec θ) i) ^ 2 + D ^ 2 * R ^ 2 * ↑n / ↑k := by
      simp only [] at h_sel
      simp_rw [h_mean] at h_sel
      exact h_sel
    have h_raw : ∑ i : Fin n, ((Φ.mulVec θ') i - f i) ^ 2 ≤
        ∑ i : Fin n, ((Φ.mulVec θ) i - f i) ^ 2 + D ^ 2 * R ^ 2 * ↑n / ↑k := by
      have eq1 : ∑ i : Fin n, ((Φ.mulVec θ') i - f i) ^ 2 =
          ∑ i : Fin n, (f i - (1 / ↑k) * ∑ l, atom (sel l) i) ^ 2 := by
        congr 1; ext i; rw [h_mulvec]; ring
      have eq2 : ∑ i : Fin n, ((Φ.mulVec θ) i - f i) ^ 2 =
          ∑ i : Fin n, (f i - (Φ.mulVec θ) i) ^ 2 := by
        congr 1; ext i; ring
      rw [eq1, eq2]; exact h_sel_rewrite
    unfold MSE
    have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
    have h_div : (1 / ↑n) * ∑ i, ((Φ.mulVec θ') i - f i) ^ 2 ≤
        (1 / ↑n) * (∑ i, ((Φ.mulVec θ) i - f i) ^ 2 + D ^ 2 * R ^ 2 * ↑n / ↑k) :=
      mul_le_mul_of_nonneg_left h_raw (by positivity)
    have h_split : (1 / ↑n) * (∑ i, ((Φ.mulVec θ) i - f i) ^ 2 + D ^ 2 * R ^ 2 * ↑n / ↑k) =
        (1 / ↑n) * ∑ i, ((Φ.mulVec θ) i - f i) ^ 2 + D ^ 2 * R ^ 2 / ↑k := by
      field_simp
    linarith

/-- Theorem 3.6 (sparse vs ℓ₁-ball comparison): for a dictionary `Φ` with
columns of squared norm at most `D² n`,
`inf_{‖θ‖₀ ≤ 2k} MSE(Φ θ, f) ≤ inf_{‖θ‖₁ ≤ R} MSE(Φ θ, f) + D² R² / k`. -/
theorem theorem_3_6_maurey
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ)
    (D : ℝ) (hD : 0 < D)
    (hNorm : ∀ j : Fin M, ∑ i : Fin n, (Φ i j) ^ 2 ≤ D ^ 2 * n)
    (k : ℕ) (hk : 1 ≤ k)
    (R : ℝ) (hR : 0 < R) :
    ⨅ θ : {θ : Fin M → ℝ // support_size θ ≤ 2 * k},
      MSE (Φ.mulVec θ.1) f ≤
    (⨅ θ : {θ : Fin M → ℝ // l1norm θ ≤ R},
      MSE (Φ.mulVec θ.1) f) + D ^ 2 * R ^ 2 / k := by
  have hbdd_sparse : BddBelow (Set.range (fun θ : {θ : Fin M → ℝ // support_size θ ≤ 2 * k} =>
      MSE (Φ.mulVec θ.1) f)) :=
    ⟨0, by rintro _ ⟨θ, rfl⟩; exact MSE_nonneg _ _⟩
  have hne_l1 : Nonempty {θ : Fin M → ℝ // l1norm θ ≤ R} :=
    ⟨⟨0, by simp [l1norm]; exact hR.le⟩⟩
  have key : ∀ θ₀ : {θ : Fin M → ℝ // l1norm θ ≤ R},
      ⨅ θ : {θ : Fin M → ℝ // support_size θ ≤ 2 * k},
        MSE (Φ.mulVec θ.1) f ≤
      MSE (Φ.mulVec θ₀.1) f + D ^ 2 * R ^ 2 / k := by
    intro ⟨θ₀, hθ₀⟩
    obtain ⟨θ', hθ'_sparse, hθ'_mse⟩ :=
      maurey_sparse_approx hn hM Φ f D hD hNorm k hk R hR θ₀ hθ₀
    calc ⨅ θ : {θ : Fin M → ℝ // support_size θ ≤ 2 * k},
          MSE (Φ.mulVec θ.1) f
        ≤ MSE (Φ.mulVec θ') f :=
          ciInf_le_of_le hbdd_sparse ⟨θ', hθ'_sparse⟩ le_rfl
      _ ≤ MSE (Φ.mulVec θ₀) f + D ^ 2 * R ^ 2 / k := hθ'_mse
  linarith [le_ciInf (fun θ₀ : {θ : Fin M → ℝ // l1norm θ ≤ R} =>
    sub_le_iff_le_add.mpr (key θ₀))]

end Chapter3
