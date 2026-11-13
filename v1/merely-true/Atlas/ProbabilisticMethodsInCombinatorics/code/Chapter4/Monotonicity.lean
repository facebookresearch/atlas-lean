/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 800000

open Finset Fintype Set

noncomputable section

namespace GraphMonotonicity

/-- Product Bernoulli weight of a configuration $\omega \in \{0,1\}^n$ under parameter $p$:
    $\prod_i p^{\omega_i} (1-p)^{1 - \omega_i}$. -/
def prodWeight (n : ℕ) (p : ℝ) (ω : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, bif ω i then p else 1 - p

/-- Probability of an event $A \subseteq \{0,1\}^n$ under the product Bernoulli $\mathrm{Ber}(p)^n$
    measure: $\sum_{\omega \in A} \prod_i p^{\omega_i} (1-p)^{1 - \omega_i}$. -/
def probConst (n : ℕ) (p : ℝ) (A : Set (Fin n → Bool)) : ℝ :=
  ∑ ω : Fin n → Bool, prodWeight n p ω * A.indicator (fun _ => (1 : ℝ)) ω

/-- Splits a sum over $\{0,1\}^{n+1}$ by conditioning on the first coordinate. -/
lemma sum_fin_succ_split (n : ℕ) (f : (Fin (n + 1) → Bool) → ℝ) :
    ∑ ω : Fin (n + 1) → Bool, f ω =
    ∑ ω : Fin n → Bool, f (Fin.cons true ω) +
    ∑ ω : Fin n → Bool, f (Fin.cons false ω) := by
  let e : (Bool × (Fin n → Bool)) ≃ (Fin (n + 1) → Bool) := Fin.consEquiv (fun _ => Bool)
  conv_lhs => rw [← e.sum_comp f]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]; rfl

/-- Factorization of the product weight after prepending a coordinate $b$. -/
lemma prodWeight_cons (n : ℕ) (p : ℝ) (b : Bool) (ω : Fin n → Bool) :
    prodWeight (n + 1) p (Fin.cons b ω) = (bif b then p else 1 - p) * prodWeight n p ω := by
  unfold prodWeight
  rw [Fin.prod_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

/-- Tower property of the product Bernoulli measure: conditioning on the first coordinate
    yields a convex combination of the conditional probabilities. -/
lemma probConst_succ (n : ℕ) (p : ℝ) (A : Set (Fin (n + 1) → Bool)) :
    probConst (n + 1) p A =
    p * probConst n p {ω | Fin.cons true ω ∈ A} +
    (1 - p) * probConst n p {ω | Fin.cons false ω ∈ A} := by
  classical
  unfold probConst
  rw [sum_fin_succ_split]
  simp only [prodWeight_cons, Set.indicator, Set.mem_setOf_eq, Bool.cond_true, Bool.cond_false]
  congr 1 <;> rw [Finset.mul_sum] <;> congr 1 <;> ext ω <;> ring

/-- The conditional event $\{\omega : (b, \omega) \in A\}$ inherits the upper-set
    (monotone) property from $A$. -/
lemma condSet_isUpperSet (n : ℕ) (b : Bool) (A : Set (Fin (n + 1) → Bool))
    (hA : IsUpperSet A) :
    IsUpperSet {ω : Fin n → Bool | Fin.cons b ω ∈ A} := by
  intro ω₁ ω₂ hle (hω₁ : Fin.cons b ω₁ ∈ A)
  show Fin.cons b ω₂ ∈ A
  apply hA _ hω₁
  intro i
  induction i using Fin.cases with
  | zero => simp [Fin.cons_zero]
  | succ j => simp [Fin.cons_succ]; exact hle j

/-- For $p \in [0, 1]$, the product weight is nonnegative. -/
lemma prodWeight_nonneg (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : Fin n → Bool) : 0 ≤ prodWeight n p ω := by
  unfold prodWeight
  apply Finset.prod_nonneg
  intro i _; cases ω i <;> simp <;> linarith

/-- For $p \in (0, 1)$, the product weight is strictly positive. -/
lemma prodWeight_pos (n : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (ω : Fin n → Bool) : 0 < prodWeight n p ω := by
  unfold prodWeight
  apply Finset.prod_pos
  intro i _; cases ω i <;> simp <;> linarith

/-- Monotonicity of `probConst` in the event: $A \subseteq B$ implies
    $\Pr_p[A] \le \Pr_p[B]$. -/
lemma probConst_mono_set (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Set (Fin n → Bool)) (h : A ⊆ B) :
    probConst n p A ≤ probConst n p B := by
  unfold probConst
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (prodWeight_nonneg n p hp0 hp1 ω)
  simp only [Set.indicator]
  split_ifs with hA hB
  · exact le_refl _
  · exact absurd (h hA) hB
  · linarith
  · exact le_refl _

/-- Strict monotonicity of `probConst` in the event: for $p \in (0, 1)$, if $A \subsetneq B$
    then $\Pr_p[A] < \Pr_p[B]$. -/
lemma probConst_strict_mono_set (n : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (A B : Set (Fin n → Bool)) (hAB : A ⊆ B) (hne : ∃ ω, ω ∈ B ∧ ω ∉ A) :
    probConst n p A < probConst n p B := by
  classical
  unfold probConst
  obtain ⟨ω₀, hω₀B, hω₀A⟩ := hne
  apply Finset.sum_lt_sum
  · intro ω _
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (prodWeight_pos n p hp0 hp1 ω))
    simp only [Set.indicator]
    split_ifs with hA hB
    · exact le_refl _
    · exact absurd (hAB hA) hB
    · linarith
    · exact le_refl _
  · exact ⟨ω₀, Finset.mem_univ _, by
      simp only [Set.indicator, hω₀B, hω₀A, if_true, if_false]
      linarith [prodWeight_pos n p hp0 hp1 ω₀]⟩

/-- Monotonicity of satisfying probability (Theorem 4.3.5): for any monotone (upper-set)
    event $A$ in $\{0,1\}^n$, the probability $\Pr_p[A]$ is nondecreasing in $p \in [0, 1]$. -/
theorem probConst_mono (n : ℕ) :
    ∀ (A : Set (Fin n → Bool)), IsUpperSet A →
    ∀ (p₁ p₂ : ℝ), 0 ≤ p₁ → p₁ ≤ p₂ → p₂ ≤ 1 →
    probConst n p₁ A ≤ probConst n p₂ A := by
  induction n with
  | zero =>
    intro A _ p₁ p₂ _ _ _
    unfold probConst prodWeight; simp
  | succ n ih =>
    intro A hA p₁ p₂ hp₁0 hp₁₂ hp₂1
    set A₀ := {ω : Fin n → Bool | Fin.cons false ω ∈ A}
    set A₁ := {ω : Fin n → Bool | Fin.cons true ω ∈ A}
    rw [probConst_succ, probConst_succ]
    have hA₀_upper : IsUpperSet A₀ := condSet_isUpperSet n false A hA
    have hA₁_upper : IsUpperSet A₁ := condSet_isUpperSet n true A hA
    have hf0_mono : probConst n p₁ A₀ ≤ probConst n p₂ A₀ :=
      ih A₀ hA₀_upper p₁ p₂ hp₁0 hp₁₂ hp₂1
    have hf1_mono : probConst n p₁ A₁ ≤ probConst n p₂ A₁ :=
      ih A₁ hA₁_upper p₁ p₂ hp₁0 hp₁₂ hp₂1
    have hf_sub : probConst n p₁ A₀ ≤ probConst n p₁ A₁ := by
      apply probConst_mono_set n p₁ hp₁0 (le_trans hp₁₂ hp₂1)
      intro ω (hω : Fin.cons false ω ∈ A)
      show Fin.cons true ω ∈ A
      apply hA _ hω
      intro i
      induction i using Fin.cases with
      | zero => simp [Fin.cons_zero]
      | succ j => simp [Fin.cons_succ]
    nlinarith

/-- If the all-true configuration lies in $A$, then $\Pr_p[A] \ge p^n$. -/
lemma probConst_lower_bound {n : ℕ} {p : ℝ} (A : Set (Fin n → Bool))
    (htop : (fun _ : Fin n => true) ∈ A) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ n ≤ probConst n p A := by
  classical
  unfold probConst
  have heq : p ^ n = prodWeight n p (fun _ => true) *
      A.indicator (fun _ => (1 : ℝ)) (fun _ => true) := by
    simp [prodWeight, Set.indicator, htop]
  rw [heq]
  apply Finset.single_le_sum (f := fun ω => prodWeight n p ω * A.indicator (fun _ => (1 : ℝ)) ω)
  · intro ω _
    apply mul_nonneg (prodWeight_nonneg n p hp0 hp1 ω)
    simp [Set.indicator]; split_ifs <;> linarith
  · exact Finset.mem_univ _

/-- At $p = 0$, $\Pr_0[A] = 0$ whenever the all-false configuration is not in $A$
    (because the entire mass concentrates there). -/
lemma probConst_at_zero {n : ℕ} (A : Set (Fin n → Bool))
    (hbot : (fun _ : Fin n => false) ∉ A) :
    probConst n 0 A = 0 := by
  classical
  unfold probConst
  apply Finset.sum_eq_zero
  intro ω _
  by_cases hall : ω = fun _ => false
  · simp [Set.indicator, hall, hbot]
  · have ⟨i, hi⟩ : ∃ i, ω i = true := by
      by_contra h; push_neg at h
      apply hall; ext i
      cases hb : ω i <;> simp_all
    have : prodWeight n 0 ω = 0 := by
      unfold prodWeight
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    rw [this, zero_mul]

/-- Strict monotonicity of satisfying probability (Theorem 4.3.5, strict version): for any
    nontrivial monotone event $A$ in $\{0,1\}^n$ (containing the all-true configuration but
    not the all-false one), $p \mapsto \Pr_p[A]$ is strictly increasing on $[0, 1]$. -/
theorem probConst_strictMono :
    ∀ (n : ℕ), 0 < n → ∀ (A : Set (Fin n → Bool)), IsUpperSet A →
    (fun _ : Fin n => false) ∉ A → (fun _ : Fin n => true) ∈ A →
    ∀ (p₁ p₂ : ℝ), 0 ≤ p₁ → p₁ < p₂ → p₂ ≤ 1 →
    probConst n p₁ A < probConst n p₂ A := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro _ A hA hbot htop p₁ p₂ hp₁0 hp₁₂ hp₂1
    set A₀ := {ω : Fin m → Bool | Fin.cons false ω ∈ A}
    set A₁ := {ω : Fin m → Bool | Fin.cons true ω ∈ A}
    have hA₀_upper : IsUpperSet A₀ := condSet_isUpperSet m false A hA
    have hA₁_upper : IsUpperSet A₁ := condSet_isUpperSet m true A hA
    have hA₀_sub : A₀ ⊆ A₁ := by
      intro ω (hω : Fin.cons false ω ∈ A)
      show Fin.cons true ω ∈ A
      apply hA _ hω
      intro i; induction i using Fin.cases with
      | zero => simp [Fin.cons_zero]
      | succ j => simp [Fin.cons_succ]
    have htop_A₁ : (fun _ : Fin m => true) ∈ A₁ := by
      show Fin.cons true (fun _ => true) ∈ A
      have : Fin.cons true (fun _ : Fin m => true) = (fun _ : Fin (m+1) => true) := by
        ext i; induction i using Fin.cases with
        | zero => simp [Fin.cons_zero]
        | succ j => simp [Fin.cons_succ]
      rw [this]; exact htop
    have hbot_A₀ : (fun _ : Fin m => false) ∉ A₀ := by
      intro (h : Fin.cons false (fun _ : Fin m => false) ∈ A)
      apply hbot
      have key : Fin.cons false (fun _ : Fin m => false) = (fun _ : Fin (m+1) => false) := by
        ext i; induction i using Fin.cases with
        | zero => simp [Fin.cons_zero]
        | succ j => simp [Fin.cons_succ]
      rw [key] at h; exact h
    rw [probConst_succ, probConst_succ]
    have hf0_mono : probConst m p₁ A₀ ≤ probConst m p₂ A₀ :=
      probConst_mono m A₀ hA₀_upper p₁ p₂ hp₁0 (le_of_lt hp₁₂) hp₂1
    have hf1_mono : probConst m p₁ A₁ ≤ probConst m p₂ A₁ :=
      probConst_mono m A₁ hA₁_upper p₁ p₂ hp₁0 (le_of_lt hp₁₂) hp₂1
    by_cases hA_eq : A₁ ⊆ A₀
    ·
      have hA_eq' : A₀ = A₁ := Set.Subset.antisymm hA₀_sub hA_eq
      have hsimp₁ : p₁ * probConst m p₁ A₁ + (1 - p₁) * probConst m p₁ A₀ =
          probConst m p₁ A₁ := by rw [← hA_eq']; ring
      have hsimp₂ : p₂ * probConst m p₂ A₁ + (1 - p₂) * probConst m p₂ A₀ =
          probConst m p₂ A₁ := by rw [← hA_eq']; ring
      rw [hsimp₁, hsimp₂]
      have hbot_A₁ : (fun _ : Fin m => false) ∉ A₁ := hA_eq' ▸ hbot_A₀
      rcases Nat.eq_zero_or_pos m with rfl | hm_pos
      · exfalso
        have : (fun _ : Fin 0 => false) = (fun _ : Fin 0 => true) := by
          ext i; exact Fin.elim0 i
        exact hbot_A₁ (this ▸ htop_A₁)
      · exact ih hm_pos A₁ hA₁_upper hbot_A₁ htop_A₁ p₁ p₂ hp₁0 hp₁₂ hp₂1
    ·
      have hne : ∃ ω, ω ∈ A₁ ∧ ω ∉ A₀ := by
        by_contra hall; push_neg at hall; exact hA_eq hall
      rcases eq_or_lt_of_le hp₁0 with rfl | hp₁_pos
      ·
        have hf0_zero : probConst m 0 A₀ = 0 := probConst_at_zero A₀ hbot_A₀

        have hLHS : (0 : ℝ) * probConst m 0 A₁ + (1 - 0) * probConst m 0 A₀ = 0 := by
          rw [hf0_zero]; ring
        rw [hLHS]

        have h1 : 0 < probConst m p₂ A₁ :=
          lt_of_lt_of_le (show (0:ℝ) < p₂ ^ m from by positivity)
            (probConst_lower_bound A₁ htop_A₁ (le_of_lt hp₁₂) hp₂1)
        have h2 : 0 ≤ probConst m p₂ A₀ := by
          unfold probConst; apply Finset.sum_nonneg; intro ω _
          apply mul_nonneg (prodWeight_nonneg m p₂ (le_of_lt hp₁₂) hp₂1 ω)
          simp [Set.indicator]; split_ifs <;> linarith
        nlinarith
      ·
        have hp₁_lt_1 : p₁ < 1 := lt_of_lt_of_le hp₁₂ hp₂1
        have hf_strict : probConst m p₁ A₀ < probConst m p₁ A₁ :=
          probConst_strict_mono_set m p₁ hp₁_pos hp₁_lt_1 A₀ A₁ hA₀_sub hne
        nlinarith

end GraphMonotonicity
