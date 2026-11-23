/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open Finset

namespace MinCut

structure Multigraph (V : Type*) [Fintype V] [DecidableEq V] where
  edgeMult : V → V → ℕ
  symm : ∀ u v, edgeMult u v = edgeMult v u
  no_loops : ∀ v, edgeMult v v = 0

variable {V : Type*} [Fintype V] [DecidableEq V]

def Multigraph.degree (G : Multigraph V) (v : V) : ℕ :=
  ∑ u : V, G.edgeMult v u

def Multigraph.cutValue (G : Multigraph V) (S : Finset V) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, G.edgeMult u v

def Multigraph.IsMinCut (G : Multigraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧ S ≠ Finset.univ ∧
  ∀ T : Finset V, T.Nonempty → T ≠ Finset.univ → G.cutValue S ≤ G.cutValue T

lemma Multigraph.cutValue_singleton (G : Multigraph V) (v : V) :
    G.cutValue {v} = G.degree v := by
  simp only [cutValue, degree, Finset.sum_singleton]
  have h_compl : ({v} : Finset V)ᶜ = Finset.univ.erase v := by ext u; simp
  rw [h_compl]
  have := Finset.sum_erase_add Finset.univ (fun u => G.edgeMult v u) (Finset.mem_univ v)
  linarith [G.no_loops v]

theorem Multigraph.degree_ge_minCut (G : Multigraph V) (S : Finset V)
    (hS : G.IsMinCut S) (v : V) (hV : 2 ≤ Fintype.card V) :
    G.cutValue S ≤ G.degree v := by
  rw [← cutValue_singleton G v]
  exact hS.2.2 {v} (Finset.singleton_nonempty v) (by
    intro h
    have := Finset.card_singleton v
    rw [h, Finset.card_univ] at this
    omega)

theorem Multigraph.sum_degrees_ge_card_mul_minCut (G : Multigraph V) (S : Finset V)
    (hS : G.IsMinCut S) (hV : 2 ≤ Fintype.card V) :
    Fintype.card V * G.cutValue S ≤ ∑ v : V, G.degree v := by
  calc Fintype.card V * G.cutValue S
      = ∑ _v : V, G.cutValue S := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ ∑ v : V, G.degree v :=
        Finset.sum_le_sum (fun v _ => degree_ge_minCut G S hS v hV)

theorem Multigraph.mincut_edge_fraction_le (G : Multigraph V) (S : Finset V)
    (hS : G.IsMinCut S) (hV : 2 ≤ Fintype.card V)
    (hE : 0 < ∑ v : V, G.degree v) :
    (G.cutValue S : ℝ) / ((∑ v : V, G.degree v : ℝ) / 2) ≤
    2 / (Fintype.card V : ℝ) := by
  have hn_pos : (0 : ℝ) < (Fintype.card V : ℝ) := by positivity
  have hE_pos : (0 : ℝ) < (∑ v : V, (G.degree v : ℝ)) / 2 := by
    have : (0 : ℝ) < (∑ v : V, G.degree v : ℝ) := by exact_mod_cast hE
    linarith
  rw [div_le_div_iff₀ hE_pos hn_pos]
  have h_bound := sum_degrees_ge_card_mul_minCut G S hS hV
  have h_cast := @Nat.cast_le ℝ _ |>.mpr h_bound
  push_cast at h_cast ⊢
  linarith

lemma prod_range_sub_cast_eq_descFactorial (n m : ℕ) (h : m ≤ n) :
    ∏ i ∈ Finset.range m, ((n : ℝ) - ↑i) = ↑(n.descFactorial m) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Nat.cast_sub (by omega : i ≤ n)]

theorem contraction_survival_product_eq (n : ℕ) (hn : 2 ≤ n) :
    ∏ i ∈ Finset.range (n - 2), ((n : ℝ) - ↑i - 2) / ((n : ℝ) - ↑i) =
    2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  rw [Finset.prod_div_distrib]
  have hnum : ∀ i ∈ Finset.range (n - 2), ((n : ℝ) - ↑i - 2) = ((n - 2 : ℕ) : ℝ) - ↑i := by
    intro i hi
    rw [Finset.mem_range] at hi
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  rw [Finset.prod_congr rfl hnum]
  rw [prod_range_sub_cast_eq_descFactorial (n - 2) (n - 2) (le_refl _)]
  rw [Nat.descFactorial_self]
  rw [prod_range_sub_cast_eq_descFactorial n (n - 2) (by omega)]
  rw [Nat.descFactorial_eq_div (by omega : n - 2 ≤ n)]
  rw [show n - (n - 2) = 2 from by omega]
  rw [Nat.cast_div (Nat.factorial_dvd_factorial (by omega : 2 ≤ n)) (by positivity)]
  norm_num
  rw [div_div_eq_mul_div, mul_comm]
  have key : (↑n.factorial : ℝ) = ↑n * (↑n - 1) * ↑(n - 2).factorial := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp only [show m + 2 - 2 = m from by omega]
    rw [show Nat.factorial (m + 2) = (m + 2) * (m + 1) * Nat.factorial m from by
      rw [Nat.factorial_succ, Nat.factorial_succ]; ring]
    push_cast; ring
  rw [key]
  field_simp

theorem contraction_survival_product_one_sub (n : ℕ) (hn : 2 ≤ n) :
    ∏ i ∈ Finset.range (n - 2), (1 - 2 / ((n : ℝ) - ↑i)) =
    2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have h : ∀ i ∈ Finset.range (n - 2),
      1 - 2 / ((n : ℝ) - ↑i) = ((n : ℝ) - ↑i - 2) / ((n : ℝ) - ↑i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hni : (0 : ℝ) < (n : ℝ) - ↑i := by
      have : (i : ℝ) < ↑n := by exact_mod_cast show i < n from by omega
      linarith
    rw [sub_div, div_self (ne_of_gt hni)]
  rw [Finset.prod_congr rfl h]
  exact contraction_survival_product_eq n hn

noncomputable def Multigraph.contractionSurvivalProb (G : Multigraph V) (S : Finset V) : ℝ :=
  (1 - (G.cutValue S : ℝ) / ((∑ v : V, G.degree v : ℝ) / 2)) ^ (Fintype.card V - 2)

theorem Multigraph.contractionSurvivalProb_ge_prod (G : Multigraph V) (S : Finset V)
    (hS : G.IsMinCut S) (hV : 2 ≤ Fintype.card V) :
    G.contractionSurvivalProb S ≥
    ∏ i ∈ Finset.range (Fintype.card V - 2),
      (1 - 2 / ((Fintype.card V : ℝ) - ↑i)) := by
  unfold Multigraph.contractionSurvivalProb
  set n := Fintype.card V
  set c := 1 - (G.cutValue S : ℝ) / ((∑ v : V, G.degree v : ℝ) / 2)

  have hc_bound : c ≥ 1 - 2 / (n : ℝ) := by
    by_cases hE : (0 : ℕ) < ∑ v : V, G.degree v
    · have h_frac := mincut_edge_fraction_le G S hS hV hE
      show 1 - 2 / (↑n : ℝ) ≤ c
      show 1 - 2 / (↑n : ℝ) ≤ 1 - (G.cutValue S : ℝ) / ((∑ v : V, G.degree v : ℝ) / 2)
      linarith
    · push_neg at hE
      have hE0 : (∑ v : V, G.degree v : ℕ) = 0 := Nat.eq_zero_of_le_zero hE
      show 1 - 2 / (↑n : ℝ) ≤ c
      show 1 - 2 / (↑n : ℝ) ≤ 1 - (G.cutValue S : ℝ) / ((∑ v : V, G.degree v : ℝ) / 2)
      have h_sum_zero : (∑ v : V, (G.degree v : ℝ)) = 0 := by exact_mod_cast hE0
      simp only [h_sum_zero, zero_div, div_zero, sub_zero]
      have : (2 : ℝ) / (↑n : ℝ) ≥ 0 := by positivity
      linarith

  have h_base_nonneg : (0 : ℝ) ≤ 1 - 2 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity : (0:ℝ) < ↑n)]
    exact_mod_cast hV

  have h_pow : (1 - 2 / (↑n : ℝ)) ^ (n - 2) ≤ c ^ (n - 2) :=
    pow_le_pow_left₀ h_base_nonneg hc_bound.le (n - 2)

  have h_prod : (1 - 2 / (n : ℝ)) ^ (n - 2) =
      ∏ _i ∈ Finset.range (n - 2), (1 - 2 / (n : ℝ)) := by
    simp [Finset.prod_const, Finset.card_range]
  have h_prod_le : ∏ i ∈ Finset.range (n - 2), (1 - 2 / ((n : ℝ) - ↑i)) ≤
      (1 - 2 / (n : ℝ)) ^ (n - 2) := by
    rw [h_prod]
    apply Finset.prod_le_prod
    · intro i hi
      rw [Finset.mem_range] at hi
      have hni : (2 : ℝ) < (n : ℝ) - ↑i := by
        have h1 : (i : ℝ) < (n : ℝ) - 2 := by exact_mod_cast show i < n - 2 from hi
        linarith
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    · intro i hi
      rw [Finset.mem_range] at hi
      have hni : (0 : ℝ) < (n : ℝ) - ↑i := by
        have : (i : ℝ) < (n : ℝ) := by exact_mod_cast show i < n from by omega
        linarith
      have h_le : (2 : ℝ) / (n : ℝ) ≤ 2 / ((n : ℝ) - ↑i) := by
        apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) hni
        have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        linarith
      linarith
  linarith

theorem contraction_algorithm_success_prob
    (G : Multigraph V) (S : Finset V) (hS : G.IsMinCut S)
    (hV : 2 ≤ Fintype.card V) :
    G.contractionSurvivalProb S ≥
    2 / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by
  have h_decomp := Multigraph.contractionSurvivalProb_ge_prod G S hS hV
  rw [contraction_survival_product_one_sub (Fintype.card V) hV] at h_decomp
  exact h_decomp

end MinCut
