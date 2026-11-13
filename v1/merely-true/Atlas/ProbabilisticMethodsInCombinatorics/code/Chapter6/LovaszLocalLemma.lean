/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory ProbabilityTheory Set Finset ENNReal

namespace LovaszLocalLemma

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- The event $A_0$ is mutually independent (under $\mu$) of all sign choices of the events $A_i$ for $i \in S$: for every assignment of each $B_i$ to either $A_i$ or $A_i^c$, $\mu(A_0 \cap \bigcap_{i \in S} B_i) = \mu(A_0)\,\mu(\bigcap_{i \in S} B_i)$. -/
def IndepOfEvents (A₀ : Set Ω) (A : ι → Set Ω) (S : Finset ι)
    (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ B : ι → Set Ω, (∀ i ∈ S, B i = A i ∨ B i = (A i)ᶜ) →
    μ (A₀ ∩ ⋂ i ∈ S, B i) = μ A₀ * μ (⋂ i ∈ S, B i)

/-- A directed graph $G$ is a dependency digraph for the family $(A_i)_{i \in \iota}$ if, for every $i$ and every finite set $S$ of indices distinct from $i$ and not adjacent to $i$ in $G$, the event $A_i$ is mutually independent of the events $\{A_j\}_{j \in S}$. -/
def IsDependencyDigraph [Fintype ι] [DecidableEq ι] (G : Digraph ι)
    [DecidableRel G.Adj] (A : ι → Set Ω)
    (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ i : ι, ∀ S : Finset ι, (∀ j ∈ S, ¬G.Adj i j ∧ j ≠ i) →
    IndepOfEvents (A i) A S μ

/-- The out-neighborhood of $i$ in the digraph $G$, viewed as a finite set. -/
def neighbors [Fintype ι] [DecidableEq ι] (G : Digraph ι) [DecidableRel G.Adj] (i : ι) :
    Finset ι := Finset.univ.filter (G.Adj i)

set_option maxHeartbeats 800000

variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Inductive bound built from `hcond`: given a uniform conditional estimate up to size $n$, the probability of avoiding all events in $S_1 \cup S_2$ is at least $\bigl(\prod_{j \in S_1}(1 - x_j)\bigr) \cdot \mu(\bigcap_{j \in S_2} A_j^c)$ whenever $S_1, S_2$ are disjoint and $|S_1 \cup S_2| \le n$. -/
lemma relative_product_bound_bounded
    (A : ι → Set Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hA : ∀ i, MeasurableSet (A i)) (x : ι → ℝ) (hx01 : ∀ i, 0 ≤ x i ∧ x i < 1)
    (n : ℕ) (hcond : ∀ (T : Finset ι), T.card < n → ∀ (i : ι), i ∉ T →
      μ (A i ∩ ⋂ j ∈ T, (A j)ᶜ) ≤ ENNReal.ofReal (x i) * μ (⋂ j ∈ T, (A j)ᶜ))
    (S₁ S₂ : Finset ι) (hdisj : Disjoint S₁ S₂) (hcard : (S₁ ∪ S₂).card ≤ n) :
    μ (⋂ j ∈ (S₁ ∪ S₂), (A j)ᶜ) ≥
      ENNReal.ofReal (∏ j ∈ S₁, (1 - x j)) * μ (⋂ j ∈ S₂, (A j)ᶜ) := by
  revert S₂ hdisj hcard
  induction S₁ using Finset.induction_on with
  | empty => intro S₂ _ _; simp [Finset.prod_empty, ofReal_one, Finset.empty_union]
  | @insert a T₁ haT₁ ihT₁ =>
    intro S₂ hdisj hcard
    have hdisj' : Disjoint T₁ S₂ := Disjoint.mono_left (Finset.subset_insert a T₁) hdisj
    have haS₂ : a ∉ S₂ := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self a T₁)
    have haT₁S₂ : a ∉ T₁ ∪ S₂ := by simp [Finset.mem_union]; exact ⟨haT₁, haS₂⟩
    have hcard_sub : (T₁ ∪ S₂).card < n := by
      have h1 : insert a T₁ ∪ S₂ = insert a (T₁ ∪ S₂) := by simp [Finset.insert_union]
      rw [h1] at hcard; rw [Finset.card_insert_of_notMem haT₁S₂] at hcard; omega
    rw [show insert a T₁ ∪ S₂ = insert a (T₁ ∪ S₂) from by simp [Finset.insert_union]]
    rw [show (⋂ j ∈ (insert a (T₁ ∪ S₂) : Finset ι), (A j)ᶜ) =
        (A a)ᶜ ∩ (⋂ j ∈ (T₁ ∪ S₂), (A j)ᶜ) from by simp]
    rw [Finset.prod_insert haT₁]
    set B := ⋂ j ∈ (T₁ ∪ S₂), (A j)ᶜ
    have hstep : μ ((A a)ᶜ ∩ B) ≥ ENNReal.ofReal (1 - x a) * μ B := by
      have hmeas : μ ((A a)ᶜ ∩ B) = μ B - μ (A a ∩ B) := by
        have h := measure_inter_add_diff (μ := μ) B (hA a)
        rw [show B ∩ A a = A a ∩ B from inter_comm B (A a),
            show B \ A a = (A a)ᶜ ∩ B from by ext y; simp [and_comm]] at h
        rw [← h, ENNReal.add_sub_cancel_left (measure_ne_top μ _)]
      rw [hmeas, show ENNReal.ofReal (1 - x a) * μ B = μ B - ENNReal.ofReal (x a) * μ B from by
        rw [show ENNReal.ofReal (1 - x a) = 1 - ENNReal.ofReal (x a) from by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_sub 1 (hx01 a).1]
        rw [ENNReal.sub_mul (fun h1 h2 => measure_ne_top μ B)]; simp [one_mul]]
      exact tsub_le_tsub_left (hcond (T₁ ∪ S₂) hcard_sub a haT₁S₂) (μ B)
    calc μ ((A a)ᶜ ∩ B)
        ≥ ENNReal.ofReal (1 - x a) * μ B := hstep
      _ ≥ ENNReal.ofReal (1 - x a) * (ENNReal.ofReal (∏ j ∈ T₁, (1 - x j)) *
            μ (⋂ j ∈ S₂, (A j)ᶜ)) := by
          gcongr; exact ihT₁ S₂ hdisj' (le_of_lt hcard_sub)
      _ = (ENNReal.ofReal (1 - x a) * ENNReal.ofReal (∏ j ∈ T₁, (1 - x j))) *
            μ (⋂ j ∈ S₂, (A j)ᶜ) := by ring
      _ = ENNReal.ofReal ((1 - x a) * ∏ j ∈ T₁, (1 - x j)) *
            μ (⋂ j ∈ S₂, (A j)ᶜ) := by
          rw [← ENNReal.ofReal_mul (by linarith [(hx01 a).2])]

/-- The induction underlying the general Lovász Local Lemma: under the dependency-digraph hypothesis `hG` and the bound $\mu(A_i) \le x_i \prod_{j \in N(i)}(1 - x_j)$, for every finite $S$ not containing $i$ we have $\mu(A_i \cap \bigcap_{j \in S} A_j^c) \le x_i \, \mu(\bigcap_{j \in S} A_j^c)$. -/
theorem cond_prob_bound (G : Digraph ι) [DecidableRel G.Adj]
    (A : ι → Set Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hA : ∀ i, MeasurableSet (A i)) (hG : IsDependencyDigraph G A μ)
    (x : ι → ℝ) (hx01 : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hbound : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ neighbors G i, (1 - x j)))
    (S : Finset ι) (i : ι) (hiS : i ∉ S) :
    μ (A i ∩ ⋂ j ∈ S, (A j)ᶜ) ≤ ENNReal.ofReal (x i) * μ (⋂ j ∈ S, (A j)ᶜ) := by
  suffices key : ∀ (n : ℕ) (T : Finset ι) (j : ι), T.card = n → j ∉ T →
      μ (A j ∩ ⋂ k ∈ T, (A k)ᶜ) ≤ ENNReal.ofReal (x j) * μ (⋂ k ∈ T, (A k)ᶜ) from
    key S.card S i rfl hiS
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro T j hTn hjT
  set T₂ := T.filter (fun k => ¬G.Adj j k)
  set T₁ := T.filter (G.Adj j)
  have hT₂_indep : ∀ k ∈ T₂, ¬G.Adj j k ∧ k ≠ j := fun k hk => by
    have hk' := Finset.mem_filter.mp hk; exact ⟨hk'.2, fun h => hjT (h ▸ hk'.1)⟩
  have h_indep : μ (A j ∩ ⋂ k ∈ T₂, (A k)ᶜ) = μ (A j) * μ (⋂ k ∈ T₂, (A k)ᶜ) :=
    (hG j T₂ hT₂_indep) (fun k => (A k)ᶜ) (fun k _ => Or.inr rfl)
  have hmono : (⋂ k ∈ T, (A k)ᶜ) ⊆ (⋂ k ∈ T₂, (A k)ᶜ) := fun y hy =>
    mem_iInter.mpr fun k => mem_iInter.mpr fun hk =>
      mem_iInter.mp (mem_iInter.mp hy k) (Finset.mem_of_mem_filter k hk)
  have hT₁_sub : T₁ ⊆ neighbors G j := fun k hk =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ k, (Finset.mem_filter.mp hk).2⟩
  have hprod_le : x j * ∏ k ∈ neighbors G j, (1 - x k) ≤ x j * ∏ k ∈ T₁, (1 - x k) := by
    apply mul_le_mul_of_nonneg_left _ (hx01 j).1
    rw [← Finset.prod_sdiff hT₁_sub]
    exact mul_le_of_le_one_left (Finset.prod_nonneg (fun k _ => by linarith [(hx01 k).2]))
      (Finset.prod_le_one (fun k _ => by linarith [(hx01 k).2])
        (fun k _ => by linarith [(hx01 k).1]))
  have hT_eq : T = T₁ ∪ T₂ := by
    ext k; simp only [T₁, T₂, Finset.mem_union, Finset.mem_filter]; tauto
  have hdisj : Disjoint T₁ T₂ := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => absurd h1 h2)
  have h_lower : μ (⋂ k ∈ T, (A k)ᶜ) ≥
      ENNReal.ofReal (∏ k ∈ T₁, (1 - x k)) * μ (⋂ k ∈ T₂, (A k)ᶜ) := by
    conv_lhs => rw [hT_eq]
    exact relative_product_bound_bounded A μ hA x hx01 n
      (fun U hU i' hi'U => ih U.card hU U i' rfl hi'U) T₁ T₂ hdisj (by rw [← hT_eq, hTn])

  have step1 : μ (A j ∩ ⋂ k ∈ T, (A k)ᶜ) ≤
      ENNReal.ofReal (x j * ∏ k ∈ neighbors G j, (1 - x k)) * μ (⋂ k ∈ T₂, (A k)ᶜ) :=
    calc μ (A j ∩ ⋂ k ∈ T, (A k)ᶜ)
        ≤ μ (A j ∩ ⋂ k ∈ T₂, (A k)ᶜ) := measure_mono (inter_subset_inter_right _ hmono)
      _ = μ (A j) * μ (⋂ k ∈ T₂, (A k)ᶜ) := h_indep
      _ ≤ _ := by gcongr; exact hbound j
  have step2 : ENNReal.ofReal (x j * ∏ k ∈ neighbors G j, (1 - x k)) * μ (⋂ k ∈ T₂, (A k)ᶜ)
      ≤ ENNReal.ofReal (x j * ∏ k ∈ T₁, (1 - x k)) * μ (⋂ k ∈ T₂, (A k)ᶜ) :=
    mul_le_mul_left (ENNReal.ofReal_le_ofReal hprod_le) _
  have step3 : ENNReal.ofReal (x j * ∏ k ∈ T₁, (1 - x k)) * μ (⋂ k ∈ T₂, (A k)ᶜ)
      = ENNReal.ofReal (x j) * (ENNReal.ofReal (∏ k ∈ T₁, (1 - x k)) * μ (⋂ k ∈ T₂, (A k)ᶜ)) := by
    rw [ENNReal.ofReal_mul (hx01 j).1]; ring
  have step4 : ENNReal.ofReal (x j) * (ENNReal.ofReal (∏ k ∈ T₁, (1 - x k)) * μ (⋂ k ∈ T₂, (A k)ᶜ))
      ≤ ENNReal.ofReal (x j) * μ (⋂ k ∈ T, (A k)ᶜ) :=
    mul_le_mul_right h_lower _
  exact le_trans step1 (le_trans step2 (step3 ▸ step4))

/-- General Lovász Local Lemma (Theorem 6.1.9): given events $A_i$ with dependency digraph $G$ and weights $x_i \in [0,1)$ such that $\mu(A_i) \le x_i \prod_{j \in N(i)}(1 - x_j)$ for every $i$, one has $\mu(\bigcap_i \overline{A_i}) \ge \prod_i (1 - x_i)$, so in particular it is positive. -/
theorem lovasz_local_lemma_general (G : Digraph ι) [DecidableRel G.Adj]
    (A : ι → Set Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hA : ∀ i, MeasurableSet (A i)) (hG : IsDependencyDigraph G A μ)
    (x : ι → ℝ) (hx01 : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hbound : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ neighbors G i, (1 - x j))) :
    μ (⋂ i : ι, (A i)ᶜ) ≥ ENNReal.ofReal (∏ i : ι, (1 - x i)) := by
  have hcond := cond_prob_bound G A μ hA hG x hx01 hbound
  have h := relative_product_bound_bounded A μ hA x hx01
    ((Finset.univ : Finset ι).card + 1)
    (fun T hT j hjT => hcond T j hjT) Finset.univ ∅
    (Finset.disjoint_empty_right _) (by simp [Finset.card_univ])
  simp only [Finset.union_empty] at h
  have hempty : (⋂ j ∈ (∅ : Finset ι), (A j)ᶜ) = Set.univ := by simp
  rw [hempty, measure_univ, mul_one] at h
  have heq : (⋂ i : ι, (A i)ᶜ) = ⋂ j ∈ (Finset.univ : Finset ι), (A j)ᶜ := by simp
  rw [heq]; convert h using 2

omit [Fintype ι] in
/-- Weierstrass-style inequality: for $f_i \in [0,1]$ on a finite set $s$, $1 - \sum_{i \in s} f_i \le \prod_{i \in s} (1 - f_i)$. -/
lemma prod_one_sub_ge_one_sub_sum (s : Finset ι) (f : ι → ℝ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t hat ih =>
    rw [Finset.prod_insert hat, Finset.sum_insert hat]
    have hfa0 : 0 ≤ f a := hf0 a (mem_insert_self a t)
    have hfa1 : f a ≤ 1 := hf1 a (mem_insert_self a t)
    have hf0' : ∀ i ∈ t, 0 ≤ f i := fun i hi => hf0 i (mem_insert_of_mem hi)
    have hf1' : ∀ i ∈ t, f i ≤ 1 := fun i hi => hf1 i (mem_insert_of_mem hi)
    have hprod_nn : 0 ≤ ∏ i ∈ t, (1 - f i) :=
      Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (hf1' i hi))
    have ih' := ih hf0' hf1'
    have key : (1 - f a) * ∏ i ∈ t, (1 - f i) ≥ (1 - f a) * (1 - ∑ i ∈ t, f i) :=
      mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr hfa1)
    have expand : (1 - f a) * (1 - ∑ i ∈ t, f i) =
        1 - f a - ∑ i ∈ t, f i + f a * ∑ i ∈ t, f i := by ring
    have hsnn : 0 ≤ ∑ i ∈ t, f i := Finset.sum_nonneg hf0'
    linarith [mul_nonneg hfa0 hsnn]

set_option maxHeartbeats 400000

/-- Corollary 6.1.10 of LLL: if every $p_i < 1/2$ and for every $i$ the sum $\sum_{j \in N(i)} p_j \le 1/4$, then $\mu(\bigcap_i \overline{A_i}) > 0$. -/
theorem lovasz_local_lemma_cor_6_1_10 (G : Digraph ι) [DecidableRel G.Adj]
    (A : ι → Set Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hA : ∀ i, MeasurableSet (A i)) (hG : IsDependencyDigraph G A μ)
    (p : ι → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_lt : ∀ i, p i < 1 / 2)
    (hp_bound : ∀ i, μ (A i) ≤ ENNReal.ofReal (p i))
    (hp_sum : ∀ i, ∑ j ∈ neighbors G i, p j ≤ 1 / 4) :
    μ (⋂ i : ι, (A i)ᶜ) > 0 := by

  set x : ι → ℝ := fun i => 2 * p i
  have hx01 : ∀ i, 0 ≤ x i ∧ x i < 1 := fun i =>
    ⟨by simp only [x]; linarith [hp_nn i], by simp only [x]; linarith [hp_lt i]⟩

  have hbound : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ neighbors G i, (1 - x j)) := by
    intro i
    have hpi : p i ≤ x i * ∏ j ∈ neighbors G i, (1 - x j) := by

      have hf0 : ∀ j ∈ neighbors G i, (0 : ℝ) ≤ x j :=
        fun j _ => (hx01 j).1
      have hf1 : ∀ j ∈ neighbors G i, x j ≤ 1 :=
        fun j _ => le_of_lt (hx01 j).2
      have hprod_bound : (1 : ℝ) / 2 ≤ ∏ j ∈ neighbors G i, (1 - x j) := by
        have h1 : 1 - ∑ j ∈ neighbors G i, x j ≤ ∏ j ∈ neighbors G i, (1 - x j) :=
          prod_one_sub_ge_one_sub_sum _ _ hf0 hf1
        have h2 : ∑ j ∈ neighbors G i, x j = 2 * ∑ j ∈ neighbors G i, p j := by
          simp only [x, Finset.mul_sum]
        linarith [hp_sum i]

      calc p i = x i / 2 := by simp [x]
        _ = x i * (1 / 2) := by ring
        _ ≤ x i * ∏ j ∈ neighbors G i, (1 - x j) :=
            mul_le_mul_of_nonneg_left hprod_bound (hx01 i).1
    calc μ (A i) ≤ ENNReal.ofReal (p i) := hp_bound i
      _ ≤ ENNReal.ofReal (x i * ∏ j ∈ neighbors G i, (1 - x j)) :=
          ENNReal.ofReal_le_ofReal hpi

  have hlll := lovasz_local_lemma_general G A μ hA hG x hx01 hbound

  have hprod_pos : (0 : ℝ) < ∏ i : ι, (1 - x i) :=
    Finset.prod_pos (fun i _ => by have := (hx01 i).2; linarith)
  calc μ (⋂ i : ι, (A i)ᶜ)
      ≥ ENNReal.ofReal (∏ i : ι, (1 - x i)) := hlll
    _ > 0 := ENNReal.ofReal_pos.mpr hprod_pos

set_option maxHeartbeats 800000

/-- Real-analytic helper inequality $(1 - 1/(d+1))^d \ge 1/e$ for $d \ge 1$, used in the symmetric LLL. -/
lemma one_sub_inv_pow_ge_inv_exp (d : ℕ) (hd : 1 ≤ d) :
    (1 - 1 / ((d : ℝ) + 1)) ^ d ≥ 1 / Real.exp 1 := by
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hd1_pos : (0 : ℝ) < (d : ℝ) + 1 := by linarith
  have hfrac_pos : (0 : ℝ) < (d : ℝ) / ((d : ℝ) + 1) := div_pos hd_pos hd1_pos
  have hfrac_eq : 1 - 1 / ((d : ℝ) + 1) = (d : ℝ) / ((d : ℝ) + 1) := by
    have h := hd1_pos.ne'; field_simp; linarith
  rw [hfrac_eq]

  have hlog_bound : -(1 : ℝ) / d ≤ Real.log ((d : ℝ) / ((d : ℝ) + 1)) := by
    have h := Real.one_sub_inv_le_log_of_pos hfrac_pos


    rw [inv_div] at h


    have heq : (1 : ℝ) - ((d : ℝ) + 1) / (d : ℝ) = -(1 : ℝ) / d := by
      field_simp; ring
    linarith

  have hd_log_bound : -1 ≤ (d : ℝ) * Real.log ((d : ℝ) / ((d : ℝ) + 1)) := by
    have h := mul_le_mul_of_nonneg_left hlog_bound (le_of_lt hd_pos)
    have heq : (d : ℝ) * (-(1 : ℝ) / (d : ℝ)) = -1 := by field_simp
    linarith

  have hlog_pow : Real.log (((d : ℝ) / ((d : ℝ) + 1)) ^ d) = (d : ℝ) * Real.log ((d : ℝ) / ((d : ℝ) + 1)) :=
    Real.log_pow _ d

  have hpow_pos : (0 : ℝ) < ((d : ℝ) / ((d : ℝ) + 1)) ^ d := pow_pos hfrac_pos d

  rw [ge_iff_le, show (1 : ℝ) / Real.exp 1 = Real.exp (-1) from by
    rw [Real.exp_neg, one_div]]
  rw [← Real.exp_log hpow_pos]
  exact Real.exp_le_exp_of_le (by linarith [hlog_pow])

/-- Symmetric Lovász Local Lemma (Theorem 6.1.7): if each event satisfies $\mu(A_i) \le p$, the dependency digraph has maximum out-degree at most $d \ge 1$, and $e p (d+1) \le 1$, then $\mu(\bigcap_i \overline{A_i}) > 0$. -/
theorem lovasz_local_lemma_symmetric (G : Digraph ι) [DecidableRel G.Adj]
    (A : ι → Set Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hA : ∀ i, MeasurableSet (A i)) (hG : IsDependencyDigraph G A μ)
    {p : ℝ} {d : ℕ} (hp : 0 ≤ p) (hd : 1 ≤ d)
    (hprob : ∀ i, μ (A i) ≤ ENNReal.ofReal p)
    (hdeg : ∀ i, (neighbors G i).card ≤ d)
    (hcond : Real.exp 1 * p * (↑d + 1) ≤ 1) :
    μ (⋂ i : ι, (A i)ᶜ) > 0 := by

  set x : ι → ℝ := fun _ => 1 / ((d : ℝ) + 1)
  have hd_cast : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1_pos : (0 : ℝ) < (d : ℝ) + 1 := by linarith
  have hx01 : ∀ i, 0 ≤ x i ∧ x i < 1 := fun _ => by
    simp only [x]
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hd1_pos]
    linarith

  have hbound : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ neighbors G i, (1 - x j)) := by
    intro i
    have hbase_nn : (0 : ℝ) ≤ 1 - x i := by
      have := (hx01 i).2; linarith
    have hbase_le_one : 1 - x i ≤ 1 := by
      have := (hx01 i).1; linarith
    have hprod_eq : ∏ j ∈ neighbors G i, (1 - x j) = (1 - x i) ^ (neighbors G i).card := by
      simp only [x]
      exact Finset.prod_const _
    have hpow_mono : (1 - x i) ^ d ≤ (1 - x i) ^ (neighbors G i).card := by
      exact pow_le_pow_of_le_one hbase_nn hbase_le_one (hdeg i)
    have hprod_lower : x i * (1 - x i) ^ d ≤ x i * ∏ j ∈ neighbors G i, (1 - x j) := by
      rw [hprod_eq]
      exact mul_le_mul_of_nonneg_left hpow_mono (hx01 i).1
    have hinv_e_bound : 1 / (Real.exp 1 * ((d : ℝ) + 1)) ≤ x i * (1 - x i) ^ d := by
      simp only [x]
      rw [show 1 / (Real.exp 1 * ((d : ℝ) + 1)) = 1 / ((d : ℝ) + 1) * (1 / Real.exp 1) from by
        rw [mul_comm (Real.exp 1) _, one_div, one_div, one_div, mul_inv]]
      exact mul_le_mul_of_nonneg_left (one_sub_inv_pow_ge_inv_exp d hd) (by positivity)
    have hp_le : p ≤ 1 / (Real.exp 1 * ((d : ℝ) + 1)) := by
      rw [le_div_iff₀ (mul_pos (Real.exp_pos 1) hd1_pos)]
      linarith
    have hp_le' : p ≤ x i * ∏ j ∈ neighbors G i, (1 - x j) :=
      le_trans hp_le (le_trans hinv_e_bound hprod_lower)
    calc μ (A i) ≤ ENNReal.ofReal p := hprob i
      _ ≤ ENNReal.ofReal (x i * ∏ j ∈ neighbors G i, (1 - x j)) :=
          ENNReal.ofReal_le_ofReal hp_le'

  have hlll := lovasz_local_lemma_general G A μ hA hG x hx01 hbound

  have hprod_pos : (0 : ℝ) < ∏ i : ι, (1 - x i) :=
    Finset.prod_pos (fun i _ => by have := (hx01 i).2; linarith)
  calc μ (⋂ i : ι, (A i)ᶜ)
      ≥ ENNReal.ofReal (∏ i : ι, (1 - x i)) := hlll
    _ > 0 := ENNReal.ofReal_pos.mpr hprod_pos

end LovaszLocalLemma
