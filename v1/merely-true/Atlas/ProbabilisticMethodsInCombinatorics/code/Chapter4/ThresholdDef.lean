/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.Monotonicity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.MetricSpace.Basic

set_option maxHeartbeats 1600000

open Filter Finset BigOperators

namespace MonotoneProperty

/-- A property $\mathcal{F}$ of finite subsets is **monotone (increasing)** if it is closed
under taking supersets: whenever $S \subseteq T$ and $\mathcal{F}(S)$ holds, so does $\mathcal{F}(T)$. -/
def IsMonotone {α : Type*} (ℱ : Finset α → Prop) : Prop :=
  ∀ ⦃S T : Finset α⦄, S ⊆ T → ℱ S → ℱ T

/-- **Definition 4.3.1 (threshold function).** A sequence $q(n)$ is a threshold for a
monotone property with probability function $\mu_n(p)$ if $\mu_n(p_n) \to 0$ whenever
$p_n / q_n \to 0$, and $\mu_n(p_n) \to 1$ whenever $p_n / q_n \to \infty$. -/
def IsThreshold (probOfProperty : ℕ → ℝ → ℝ) (q : ℕ → ℝ) : Prop :=
  (∀ p : ℕ → ℝ, Tendsto (fun n => p n / q n) atTop (nhds 0) →
    Tendsto (fun n => probOfProperty n (p n)) atTop (nhds 0)) ∧
  (∀ p : ℕ → ℝ, Tendsto (fun n => p n / q n) atTop atTop →
    Tendsto (fun n => probOfProperty n (p n)) atTop (nhds 1))

end MonotoneProperty

namespace Threshold

/-- The probability under the product Bernoulli$(p)$ distribution on $2^\Omega$ that
the random subset is exactly one of the sets in $\mathcal{F}$, summing the
weights $p^{|A|}(1-p)^{|\Omega| - |A|}$ over $A \in \mathcal{F}$. -/
noncomputable def randomSubsetProb (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (𝓕 : Finset (Finset Ω)) (p : ℝ) : ℝ :=
  ∑ A ∈ 𝓕, p ^ A.card * (1 - p) ^ (Fintype.card Ω - A.card)

/-- A function $r(n)$ is a **sharp threshold** if for every $\delta > 0$, the probability
$\mu_n(p_n) \to 0$ whenever eventually $p_n \le (1 - \delta) r_n$, and
$\mu_n(p_n) \to 1$ whenever eventually $p_n \ge (1 + \delta) r_n$. -/
def IsSharpThreshold (μ : ℕ → ℝ → ℝ) (r : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    (∀ p : ℕ → ℝ, (∀ᶠ n in atTop, p n / r n ≤ 1 - δ) →
      Tendsto (fun n => μ n (p n)) atTop (nhds 0)) ∧
    (∀ p : ℕ → ℝ, (∀ᶠ n in atTop, p n / r n ≥ 1 + δ) →
      Tendsto (fun n => μ n (p n)) atTop (nhds 1))

/-- A function $r(n)$ is a **coarse threshold** if there exist constants $0 < c < C$ and
$\varepsilon > 0$ such that whenever $p_n / r_n \in [c, C]$ eventually, the property
probability is eventually bounded into $[\varepsilon, 1 - \varepsilon]$. -/
def IsCoarseThreshold (μ : ℕ → ℝ → ℝ) (r : ℕ → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ p : ℕ → ℝ, (∀ᶠ n in atTop, c ≤ p n / r n ∧ p n / r n ≤ C) →
      ∀ᶠ n in atTop, ε ≤ μ n (p n) ∧ μ n (p n) ≤ 1 - ε

end Threshold

namespace GraphMonotonicity

open Finset Fintype Set

/-- The product Bernoulli$(p)$ weights on $\{0,1\}^n$ sum to $1$. -/
lemma prodWeight_sum_eq_one (n : ℕ) (p : ℝ) :
    ∑ ω : Fin n → Bool, prodWeight n p ω = 1 := by
  induction n with
  | zero => simp [prodWeight]
  | succ n ih =>
    rw [sum_fin_succ_split]
    simp only [prodWeight_cons, Bool.cond_true, Bool.cond_false]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ih]
    ring

/-- For the product Bernoulli$(p)$ measure on $\{0,1\}^n$, an event and its complement
have measures summing to $1$. -/
lemma probConst_add_compl (n : ℕ) (p : ℝ) (A : Set (Fin n → Bool)) :
    probConst n p A + probConst n p Aᶜ = 1 := by
  classical
  unfold probConst
  rw [← Finset.sum_add_distrib]
  have h : ∀ ω : Fin n → Bool,
    prodWeight n p ω * A.indicator (fun _ => (1:ℝ)) ω +
    prodWeight n p ω * Aᶜ.indicator (fun _ => (1:ℝ)) ω =
    prodWeight n p ω := by
    intro ω; simp only [Set.indicator, Set.mem_compl_iff]; split_ifs <;> ring
  simp_rw [h]
  exact prodWeight_sum_eq_one n p

/-- The probability of any event under the product Bernoulli$(p)$ measure is nonnegative,
provided $0 \le p \le 1$. -/
lemma probConst_nonneg (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (Fin n → Bool)) : 0 ≤ probConst n p A := by
  unfold probConst
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg (prodWeight_nonneg n p hp0 hp1 ω)
  simp only [Set.indicator]
  split_ifs <;> linarith

/-- For an upper (monotone increasing) set $A$, the probability of its complement under
the product Bernoulli$(p)$ measure is *antitone* in $p$. -/
lemma probConst_compl_anti (n : ℕ) (A : Set (Fin n → Bool)) (hA : IsUpperSet A)
    (q p : ℝ) (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp1 : p ≤ 1) :
    probConst n p Aᶜ ≤ probConst n q Aᶜ := by
  have hq1 : q ≤ 1 := le_trans hqp hp1
  have hp0 : 0 ≤ p := le_trans hq0 hqp

  have htot_p := probConst_add_compl n p A
  have htot_q := probConst_add_compl n q A
  have hmono := probConst_mono n A hA q p hq0 hqp hp1
  linarith

/-- An algebraic convexity-style inequality used in the union-of-copies argument:
$(1 - s^m)\alpha^m + s^m \beta^m \le ((1-s)\alpha + s\beta)^m$ for $0 \le \alpha \le \beta$
and $s \in [0,1]$. -/
theorem union_copies_ineq (α β s : ℝ) (hα0 : 0 ≤ α) (hαβ : α ≤ β)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ m : ℕ, 1 ≤ m →
    (1 - s ^ m) * α ^ m + s ^ m * β ^ m ≤ ((1 - s) * α + s * β) ^ m := by
  have hβ0 : 0 ≤ β := le_trans hα0 hαβ
  have hw0 : 0 ≤ (1 - s) * α + s * β := by nlinarith
  have hw_ge_α : α ≤ (1 - s) * α + s * β := by nlinarith
  intro m hm
  induction m with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simp only [Nat.zero_add, pow_one]
      linarith
    | succ k =>
      have ih' := ih (by omega : 1 ≤ k + 1)
      have hpow_mono : α ^ (k + 1) ≤ β ^ (k + 1) := by gcongr
      set w := (1 - s) * α + s * β with hw_def
      suffices h : (1 - s ^ (k + 2)) * α ^ (k + 2) + s ^ (k + 2) * β ^ (k + 2) ≤
        (1 - s ^ (k + 1)) * α ^ (k + 2) + (1 - s) * s ^ (k + 1) * α * β ^ (k + 1) +
        s ^ (k + 2) * β ^ (k + 2) by
        calc w ^ (k + 2)
            = w * w ^ (k + 1) := by ring
          _ ≥ w * ((1 - s ^ (k + 1)) * α ^ (k + 1) + s ^ (k + 1) * β ^ (k + 1)) :=
              mul_le_mul_of_nonneg_left ih' hw0
          _ = (1 - s ^ (k + 1)) * w * α ^ (k + 1) + s ^ (k + 1) * w * β ^ (k + 1) := by ring
          _ ≥ (1 - s ^ (k + 1)) * α * α ^ (k + 1) + s ^ (k + 1) * w * β ^ (k + 1) := by
              have hs_le : s ^ (k + 1) ≤ 1 := pow_le_one₀ hs0 hs1
              nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s ^ (k+1))
                         (pow_nonneg hα0 (k+1))]
          _ = (1 - s ^ (k + 1)) * α ^ (k + 2) + s ^ (k + 1) * w * β ^ (k + 1) := by ring
          _ = (1 - s ^ (k + 1)) * α ^ (k + 2) +
              (1 - s) * s ^ (k + 1) * α * β ^ (k + 1) +
              s ^ (k + 2) * β ^ (k + 2) := by rw [hw_def]; ring
          _ ≥ _ := by linarith
      suffices hsuff : (1 - s) * s ^ (k + 1) * α * β ^ (k + 1) ≥
        (s ^ (k + 1) - s ^ (k + 2)) * α ^ (k + 2) by linarith
      have heq : s ^ (k + 1) - s ^ (k + 2) = (1 - s) * s ^ (k + 1) := by ring
      rw [heq]
      have h1 : 0 ≤ (1 - s) * s ^ (k + 1) * α := by
        apply mul_nonneg
        · apply mul_nonneg (by linarith) (pow_nonneg hs0 _)
        · exact hα0
      have h2 : (1 - s) * s ^ (k + 1) * α * α ^ (k + 1) ≤
        (1 - s) * s ^ (k + 1) * α * β ^ (k + 1) :=
        mul_le_mul_of_nonneg_left hpow_mono h1
      have h3 : (1 - s) * s ^ (k + 1) * α ^ (k + 2) =
        (1 - s) * s ^ (k + 1) * α * α ^ (k + 1) := by ring
      linarith

/-- **Bernoulli's inequality (complement form).** For $m \ge 1$ and $p/m \le 1$,
$1 - p \le (1 - p/m)^m$. -/
theorem bernoulli_complement (p : ℝ) (m : ℕ) (hm : 1 ≤ m) (hpm : p / (m : ℝ) ≤ 1) :
    1 - p ≤ (1 - p / ↑m) ^ m := by
  have h1 : -1 ≤ (1 - p / ↑m : ℝ) := by linarith
  have key := one_add_mul_sub_le_pow h1 m
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have heq : 1 + ↑m * (1 - p / ↑m - 1) = 1 - p := by field_simp; ring
  linarith

/-- **Union of independent copies bound.** For an upper set $A$ on $\{0,1\}^n$, the
probability of $A^c$ under Bernoulli$(1 - (1-t)^m)$ is at most the $m$-th power of the
probability of $A^c$ under Bernoulli$(t)$. -/
theorem probConst_compl_union_bound (n : ℕ) :
    ∀ (A : Set (Fin n → Bool)), IsUpperSet A →
    ∀ (t : ℝ), 0 ≤ t → t ≤ 1 →
    ∀ (m : ℕ), 1 ≤ m →
    probConst n (1 - (1 - t) ^ m) Aᶜ ≤ (probConst n t Aᶜ) ^ m := by
  induction n with
  | zero =>
    intro A _ t _ _ m hm
    unfold probConst prodWeight
    simp only [Fintype.sum_unique, Finset.prod_empty, one_mul, Set.indicator]
    split_ifs with h
    · simp [one_pow]
    · simp [zero_pow (by omega : m ≠ 0)]
  | succ n ih =>
    intro A hA t ht0 ht1 m hm
    set A₁ := {ω : Fin n → Bool | Fin.cons true ω ∈ A}
    set A₀ := {ω : Fin n → Bool | Fin.cons false ω ∈ A}
    have hA₁_upper : IsUpperSet A₁ := condSet_isUpperSet n true A hA
    have hA₀_upper : IsUpperSet A₀ := condSet_isUpperSet n false A hA
    have hA₀_sub_A₁ : A₀ ⊆ A₁ := by
      intro ω (hω : Fin.cons false ω ∈ A)
      show Fin.cons true ω ∈ A
      apply hA _ hω
      intro i; induction i using Fin.cases with
      | zero => simp [Fin.cons_zero]
      | succ j => simp [Fin.cons_succ]
    have hcompl_sub : A₁ᶜ ⊆ A₀ᶜ := Set.compl_subset_compl.mpr hA₀_sub_A₁
    set q := 1 - (1 - t) ^ m
    have hs : 0 ≤ 1 - t := by linarith
    have hs1 : 1 - t ≤ 1 := by linarith
    have hq0 : 0 ≤ q := by
      simp only [q]
      linarith [pow_le_one₀ hs hs1 (n := m)]
    have hq1 : q ≤ 1 := by simp only [q]; linarith [pow_nonneg hs m]

    have decomp_q : probConst (n + 1) q Aᶜ =
        q * probConst n q A₁ᶜ + (1 - q) * probConst n q A₀ᶜ := by
      have h := probConst_succ n q Aᶜ
      convert h using 2 <;> ext ω <;> simp [A₁, A₀, Set.mem_compl_iff, Set.mem_setOf_eq]
    have decomp_t : probConst (n + 1) t Aᶜ =
        t * probConst n t A₁ᶜ + (1 - t) * probConst n t A₀ᶜ := by
      have h := probConst_succ n t Aᶜ
      convert h using 2 <;> ext ω <;> simp [A₁, A₀, Set.mem_compl_iff, Set.mem_setOf_eq]

    have ih₁ : probConst n q A₁ᶜ ≤ (probConst n t A₁ᶜ) ^ m :=
      ih A₁ hA₁_upper t ht0 ht1 m hm
    have ih₀ : probConst n q A₀ᶜ ≤ (probConst n t A₀ᶜ) ^ m :=
      ih A₀ hA₀_upper t ht0 ht1 m hm

    set α := probConst n t A₁ᶜ
    set β := probConst n t A₀ᶜ
    have hα0 : 0 ≤ α := probConst_nonneg n t ht0 ht1 A₁ᶜ
    have hαβ : α ≤ β := probConst_mono_set n t ht0 ht1 A₁ᶜ A₀ᶜ hcompl_sub

    have hLHS : probConst (n + 1) q Aᶜ ≤ q * α ^ m + (1 - q) * β ^ m := by
      rw [decomp_q]
      have h1 : q * probConst n q A₁ᶜ ≤ q * α ^ m :=
        mul_le_mul_of_nonneg_left ih₁ hq0
      have h2 : (1 - q) * probConst n q A₀ᶜ ≤ (1 - q) * β ^ m :=
        mul_le_mul_of_nonneg_left ih₀ (by linarith)
      linarith

    have halg : q * α ^ m + (1 - q) * β ^ m ≤ (t * α + (1 - t) * β) ^ m := by
      have hq_eq : q = 1 - (1 - t) ^ m := by simp [q]
      have h1q_eq : 1 - q = (1 - t) ^ m := by simp [q]
      rw [hq_eq, h1q_eq]
      have key := union_copies_ineq α β (1 - t) hα0 hαβ hs hs1 m hm
      have heq : (1 - (1 - t)) * α + (1 - t) * β = t * α + (1 - t) * β := by ring
      linarith [heq ▸ key]

    calc probConst (n + 1) q Aᶜ
        ≤ q * α ^ m + (1 - q) * β ^ m := hLHS
      _ ≤ (t * α + (1 - t) * β) ^ m := halg
      _ = (probConst (n + 1) t Aᶜ) ^ m := by rw [← decomp_t]

/-- **Multi-round exposure inequality.** For an upper set $A$, the probability that a
single Bernoulli$(p)$ trial fails to land in $A$ is bounded by the $m$-th power of the
failure probability for Bernoulli$(p/m)$. -/
theorem multi_round_exposure (n : ℕ) (A : Set (Fin n → Bool)) (hA : IsUpperSet A)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (hm : 1 ≤ m) :
    probConst n p Aᶜ ≤ (probConst n (p / ↑m) Aᶜ) ^ m := by
  set t := p / (↑m : ℝ) with ht_def
  have hm_pos : (0 : ℝ) < (↑m : ℝ) := Nat.cast_pos.mpr (by omega)
  have ht0 : 0 ≤ t := div_nonneg hp0 (le_of_lt hm_pos)
  have ht1 : t ≤ 1 := by
    rw [ht_def, div_le_one hm_pos]
    exact le_trans hp1 (by exact_mod_cast hm)

  set q := 1 - (1 - t) ^ m with hq_def
  have hq_le_p : q ≤ p := by
    simp only [q, t]
    linarith [bernoulli_complement p m hm ht1]
  have hs : 0 ≤ 1 - t := by linarith
  have hq0 : 0 ≤ q := by
    simp only [q]
    linarith [pow_le_one₀ hs (by linarith : 1 - t ≤ 1) (n := m)]

  have h_anti : probConst n p Aᶜ ≤ probConst n q Aᶜ :=
    probConst_compl_anti n A hA q p hq0 hq_le_p hp1

  have h_union : probConst n q Aᶜ ≤ (probConst n t Aᶜ) ^ m := by
    have : q = 1 - (1 - t) ^ m := rfl
    rw [this]
    exact probConst_compl_union_bound n A hA t ht0 ht1 m hm
  linarith

end GraphMonotonicity

namespace MonotoneProperty

open Filter Real Set Metric

/-- The inequality $(1 - 1/m)^m < 1/2$ for $m \ge 1$, obtained from
$(1 - 1/m)^m \le e^{-1} < 1/2$. -/
lemma one_sub_inv_pow_lt_half (m : ℕ) (hm : 1 ≤ m) : (1 - 1 / (m:ℝ)) ^ m < 1 / 2 := by
  have hm_pos : (0:ℝ) < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  have h0 : (0:ℝ) ≤ 1 - 1 / (m:ℝ) := by
    rw [sub_nonneg, div_le_one hm_pos]; exact_mod_cast hm
  calc (1 - 1/(m:ℝ))^m
      ≤ (Real.exp (-(1/(m:ℝ))))^m := by
        apply pow_le_pow_left₀ h0; linarith [Real.add_one_le_exp (-(1/(m:ℝ)))]
    _ = Real.exp (-1) := by rw [← Real.exp_nat_mul]; congr 1; field_simp
    _ < 1 / 2 := by
        rw [Real.exp_neg, show (1:ℝ)/2 = (2:ℝ)⁻¹ from by norm_num]
        exact (inv_lt_inv₀ (Real.exp_pos 1) (by norm_num : (0:ℝ) < 2)).mpr
          (by linarith [Real.exp_one_gt_d9])

/-- **Existence of a threshold (Theorem 4.3.5/4.3.6).** Any monotone graph property $\mu_n$
satisfying the multi-round exposure inequality and reaching value $1/2$ at $q(n)$ has $q$
as a threshold function. -/
theorem existence_of_threshold
    (μ : ℕ → ℝ → ℝ) (q : ℕ → ℝ)
    (h_mono : ∀ n, ∀ p₁ p₂ : ℝ, 0 ≤ p₁ → p₁ ≤ p₂ → p₂ ≤ 1 → μ n p₁ ≤ μ n p₂)
    (h_ext_low : ∀ n p, p ≤ 0 → μ n p = 0)
    (h_ext_high : ∀ n p, 1 ≤ p → μ n p = 1)
    (h_mre : ∀ n p, 0 ≤ p → p ≤ 1 → ∀ m : ℕ, 1 ≤ m →
      1 - μ n p ≤ (1 - μ n (p / ↑m)) ^ m)
    (h_crit : ∀ n, μ n (q n) = 1 / 2)
    (hq_pos : ∀ n, 0 < q n)
    (hq_le : ∀ n, q n ≤ 1)
    (h_range : ∀ n p, 0 ≤ μ n p ∧ μ n p ≤ 1) :
    IsThreshold μ q := by

  have key_bound : ∀ n (m : ℕ), 1 ≤ m → μ n (q n / ↑m) < 1 / (↑m : ℝ) := by
    intro n m hm
    set x := μ n (q n / ↑m)
    have hx_range := h_range n (q n / ↑m)
    have h_applied := h_mre n (q n) (le_of_lt (hq_pos n)) (hq_le n) m hm
    rw [h_crit n] at h_applied

    by_contra h
    push_neg at h
    have : (1 - x) ^ m ≤ (1 - 1 / (m:ℝ)) ^ m :=
      pow_le_pow_left₀ (by linarith [hx_range.2]) (by linarith) m
    linarith [one_sub_inv_pow_lt_half m hm]
  constructor
  ·
    intro p hp
    rw [Metric.tendsto_nhds]
    intro ε hε

    obtain ⟨m, hm1, hm_bound⟩ : ∃ m : ℕ, 1 ≤ m ∧ 1 / (m:ℝ) < ε := by
      obtain ⟨m, hm⟩ := exists_nat_gt (1/ε)
      have h1ε : (0:ℝ) < 1 / ε := div_pos one_pos hε
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by intro h; simp [h] at hm; linarith)
      have hm_pos : (0:ℝ) < (m:ℝ) := Nat.cast_pos.mpr (by omega)
      exact ⟨m, hm1, by
        rw [div_lt_iff₀ hm_pos]
        linarith [(div_lt_iff₀ hε).mp (by linarith : 1/ε < (m:ℝ))]⟩
    have hm_pos : (0:ℝ) < (m:ℝ) := Nat.cast_pos.mpr (by omega)

    have hev : ∀ᶠ n in atTop, p n / q n < 1 / (m:ℝ) :=
      hp (Iio_mem_nhds (div_pos one_pos hm_pos))
    exact hev.mono (fun n hn => by
      simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (h_range n (p n)).1]
      by_cases hpn : p n ≤ 0
      · rw [h_ext_low n (p n) hpn]; exact hε
      · push_neg at hpn

        have hpn_lt : p n < q n / (m:ℝ) := by
          rw [div_lt_div_iff₀ (hq_pos n) hm_pos] at hn
          rw [lt_div_iff₀ hm_pos]; linarith
        have hqm_le : q n / (m:ℝ) ≤ 1 := by
          rw [div_le_one hm_pos]; exact le_trans (hq_le n) (by exact_mod_cast hm1)
        calc μ n (p n) ≤ μ n (q n / ↑m) :=
              h_mono n (p n) (q n / ↑m) (le_of_lt hpn) (le_of_lt hpn_lt) hqm_le
          _ < 1 / (↑m : ℝ) := key_bound n m hm1
          _ < ε := hm_bound)
  ·
    intro p hp
    rw [Metric.tendsto_nhds]
    intro ε hε

    obtain ⟨m, hm1, hm_bound⟩ : ∃ m : ℕ, 1 ≤ m ∧ (1/2:ℝ) ^ m < ε := by
      have h_tend := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by linarith : (0:ℝ) ≤ 1/2) (by linarith : (1:ℝ)/2 < 1)
      have hev : ∀ᶠ n in atTop, (1/2:ℝ) ^ n < ε := h_tend (Iio_mem_nhds hε)
      rw [Filter.eventually_atTop] at hev
      obtain ⟨N, hN⟩ := hev
      exact ⟨max N 1, le_max_right _ _, hN (max N 1) (le_max_left _ _)⟩

    have hev : ∀ᶠ n in atTop, (m:ℝ) ≤ p n / q n := hp (Ici_mem_atTop (m:ℝ))
    exact hev.mono (fun n hn => by
      simp only [Real.dist_eq]
      have hpn_ge : (m:ℝ) * q n ≤ p n := by rwa [le_div_iff₀ (hq_pos n)] at hn
      by_cases hpn : 1 ≤ p n
      · rw [h_ext_high n (p n) hpn]; simp; linarith
      · push_neg at hpn

        have hmq_le : (m:ℝ) * q n ≤ 1 := by linarith
        have hmq0 : (0:ℝ) ≤ (m:ℝ) * q n :=
          mul_nonneg (Nat.cast_nonneg m) (le_of_lt (hq_pos n))


        have hm_pos : (0:ℝ) < (m:ℝ) := Nat.cast_pos.mpr (by omega)
        have h_applied := h_mre n ((m:ℝ) * q n) hmq0 hmq_le m hm1
        have heq : (m:ℝ) * q n / (m:ℝ) = q n := by field_simp
        rw [heq, h_crit n] at h_applied
        have h_mono_applied : μ n ((m:ℝ) * q n) ≤ μ n (p n) :=
          h_mono n _ _ hmq0 hpn_ge (le_of_lt hpn)
        rw [abs_lt]
        constructor
        · linarith [(h_range n (p n)).2]
        · linarith [(h_range n (p n)).2])

end MonotoneProperty

namespace MonotoneProperty

/-- A monotone property is **nontrivial** if $\mu_n(0) = 0$ and $\mu_n(1) = 1$ for all $n$. -/
def IsNontrivial (μ : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, μ n 0 = 0) ∧ (∀ n, μ n 1 = 1)

end MonotoneProperty
