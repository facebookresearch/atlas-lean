/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option maxHeartbeats 400000

namespace DominatingSet

open SimpleGraph Finset Real BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A set $D \subseteq V$ is a dominating set of $G$ if every vertex outside $D$ has a
neighbor in $D$. -/
def IsDominatingSet (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : Prop :=
  ∀ v : V, v ∉ D → ∃ u ∈ D, G.Adj v u

/-- Given any subset $S \subseteq V$, augmenting it with the vertices $Y$ that are neither in
$S$ nor adjacent to $S$ produces a dominating set of size at most $|S| + |Y|$. -/
lemma exists_dominating_from_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hδ : 1 ≤ G.minDegree) :
    ∃ D : Finset V, IsDominatingSet G D ∧
      D.card ≤ S.card + (Finset.univ.filter fun v =>
        v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S).card := by
  classical
  set Y := Finset.univ.filter fun v => v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S
  refine ⟨S ∪ Y, ?_, Finset.card_union_le S Y⟩
  intro v hv
  simp only [Finset.mem_union] at hv; push_neg at hv
  obtain ⟨hvS, hvY⟩ := hv
  simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or] at hvY
  rcases hvY with h | h
  · exact absurd hvS h
  · push_neg at h
    obtain ⟨u, hu_nbr, huS⟩ := h
    exact ⟨u, Finset.mem_union_left _ huS, (mem_neighborFinset G v u).mp hu_nbr⟩

/-- The Bernoulli probability weight of a subset $S \subseteq V$ under independent inclusion
with parameter $p$: equals $p^{|S|} (1-p)^{n-|S|}$ where $n = |V|$. -/
noncomputable def bernoulliWeight (p : ℝ) (S : Finset V) : ℝ :=
  p ^ S.card * (1 - p) ^ (Fintype.card V - S.card)

/-- The Bernoulli weights sum to $1$ over all subsets of $V$, expressing that the
random subset distribution is a probability measure. -/
lemma bernoulliWeight_total (p : ℝ) :
    ∑ S ∈ (Finset.univ : Finset V).powerset, bernoulliWeight p S = 1 := by
  simp only [bernoulliWeight]
  have h := Finset.sum_pow_mul_eq_add_pow p (1 - p) (Finset.univ : Finset V)
  simp only [Finset.card_univ, add_sub_cancel, one_pow] at h
  linarith [h]

/-- The expected cost $|S| + |Y(S)|$ under the Bernoulli($p$) distribution is bounded by
$np + n(1-p)^{\delta + 1}$, where $\delta$ is the minimum degree of $G$. -/
lemma bernoulliWeight_expected_cost_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ℝ) (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hδ : 1 ≤ G.minDegree) :
    ∑ S ∈ (Finset.univ : Finset V).powerset,
      bernoulliWeight p S * ((S.card : ℝ) +
        ((Finset.univ.filter fun v => v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S).card : ℝ)) ≤
      (Fintype.card V : ℝ) * p + (Fintype.card V : ℝ) * (1 - p) ^ (G.minDegree + 1) := by
  set n := Fintype.card V
  set δ := G.minDegree
  have hsplit : ∀ S ∈ (Finset.univ : Finset V).powerset,
      bernoulliWeight p S * ((S.card : ℝ) +
        ((Finset.univ.filter fun v => v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S).card : ℝ)) =
      bernoulliWeight p S * (S.card : ℝ) +
        bernoulliWeight p S * ((Finset.univ.filter fun v =>
          v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S).card : ℝ) := by
    intro S _; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hbw_nn : ∀ S ∈ (Finset.univ : Finset V).powerset, (0 : ℝ) ≤ bernoulliWeight p S :=
    fun S _ => mul_nonneg (pow_nonneg (le_of_lt hp_pos) _) (pow_nonneg (by linarith) _)
  apply add_le_add
  ·
    suffices h1 : ∑ S ∈ (Finset.univ : Finset V).powerset,
        bernoulliWeight p S * (S.card : ℝ) = (n : ℝ) * p from le_of_eq h1

    have hcard_ind : ∀ S : Finset V,
        (S.card : ℝ) = ∑ v ∈ (Finset.univ : Finset V),
          if v ∈ S then (1 : ℝ) else 0 := by
      intro S
      have h := Finset.card_filter (· ∈ S) Finset.univ
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at h
      exact_mod_cast h
    conv_lhs => arg 2; ext S; rw [hcard_ind S, Finset.mul_sum]
    rw [Finset.sum_comm]

    simp_rw [show ∀ (v : V) (S : Finset V),
      bernoulliWeight p S * (if v ∈ S then (1 : ℝ) else 0) =
      if v ∈ S then bernoulliWeight p S else 0 from fun v S => by split_ifs <;> ring]
    simp_rw [← Finset.sum_filter]

    suffices hv : ∀ v ∈ (Finset.univ : Finset V),
        ∑ S ∈ (Finset.univ : Finset V).powerset.filter (v ∈ ·), bernoulliWeight p S = p by
      rw [Finset.sum_congr rfl hv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    intro v _


    simp only [bernoulliWeight]
    set C := Finset.univ.erase v
    have hfilt_eq : (univ : Finset V).powerset.filter (v ∈ ·) =
        C.powerset.image (insert v) := by
      ext S; simp only [mem_filter, mem_powerset, mem_image, C]
      constructor
      · intro ⟨hSu, hv⟩
        exact ⟨S.erase v, erase_subset_erase _ hSu, insert_erase hv⟩
      · rintro ⟨T, hT, rfl⟩
        exact ⟨insert_subset (mem_univ v) (hT.trans (erase_subset _ _)),
          mem_insert_self _ _⟩
    rw [hfilt_eq, sum_image]
    · have hrewrite : ∀ T ∈ C.powerset,
          p ^ (insert v T).card * (1 - p) ^ (Fintype.card V - (insert v T).card) =
          p * (p ^ T.card * (1 - p) ^ (C.card - T.card)) := by
        intro T hT
        have hv_nmem : v ∉ T := fun hv => (mem_erase.mp ((mem_powerset.mp hT) hv)).1 rfl
        rw [card_insert_of_notMem hv_nmem]
        have hTC : T.card ≤ C.card := card_le_card (mem_powerset.mp hT)
        have hcard : Fintype.card V - (T.card + 1) = C.card - T.card := by
          simp [C, card_erase_of_mem (mem_univ v)]; omega
        rw [hcard, pow_succ]; ring
      rw [sum_congr rfl hrewrite, ← mul_sum]
      have h := sum_pow_mul_eq_add_pow p (1 - p) C
      simp only [add_sub_cancel, one_pow] at h
      rw [h, mul_one]
    · intro T₁ hT₁ T₂ hT₂ h
      have hv1 : v ∉ T₁ := fun hv => (mem_erase.mp ((mem_powerset.mp hT₁) hv)).1 rfl
      have hv2 : v ∉ T₂ := fun hv => (mem_erase.mp ((mem_powerset.mp hT₂) hv)).1 rfl
      rw [← erase_insert hv1, ← erase_insert hv2, h]

  ·
    have hcard_ind2 : ∀ S : Finset V,
        ((Finset.univ.filter fun v => v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S).card : ℝ) =
        ∑ v ∈ (Finset.univ : Finset V),
          if v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S then (1 : ℝ) else 0 := by
      intro S
      exact_mod_cast Finset.card_filter
        (fun v => v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S) Finset.univ
    conv_lhs => arg 2; ext S; rw [hcard_ind2 S, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [show ∀ (v : V) (S : Finset V),
      bernoulliWeight p S * (if v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S then (1 : ℝ) else 0) =
      if v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S then bernoulliWeight p S else 0 from
      fun v S => by split_ifs <;> ring]
    simp_rw [← Finset.sum_filter]

    calc ∑ v ∈ (Finset.univ : Finset V),
          ∑ S ∈ (Finset.univ : Finset V).powerset.filter (fun S =>
            v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S), bernoulliWeight p S
        ≤ ∑ _v ∈ (Finset.univ : Finset V), (1 - p) ^ (δ + 1) := by
          apply Finset.sum_le_sum; intro v _

          set CN := Finset.cons v (G.neighborFinset v) (notMem_neighborFinset_self G v)
          have hCN_card : CN.card = G.degree v + 1 := by
            simp [CN, Finset.card_cons, card_neighborFinset_eq_degree]
          have hfilt_sub : (Finset.univ.powerset.filter fun S =>
              v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S) ⊆ (Finset.univ \ CN).powerset := by
            intro S hS
            simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
            intro x hx
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, CN, Finset.mem_cons]
            intro h; rcases h with rfl | h
            · exact hS.2.1 hx
            · exact hS.2.2 _ h hx
          calc ∑ S ∈ Finset.univ.powerset.filter (fun S =>
                v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S), bernoulliWeight p S
              ≤ ∑ S ∈ (Finset.univ \ CN).powerset, bernoulliWeight p S :=
                Finset.sum_le_sum_of_subset_of_nonneg hfilt_sub
                  (fun S _ _ => hbw_nn S (Finset.mem_powerset.mpr (Finset.subset_univ S)))
            _ ≤ (1 - p) ^ (δ + 1) := by


                simp only [bernoulliWeight]
                set Comp := Finset.univ \ CN
                have hComp_card : Comp.card = Fintype.card V - CN.card := by
                  have : CN ∩ univ = CN := inter_comm univ CN ▸ univ_inter CN
                  simp [Comp, Finset.card_sdiff, this]
                have hCN_le : CN.card ≤ Fintype.card V := card_le_card (subset_univ CN)
                have hsub : ∀ S ∈ Comp.powerset,
                    Fintype.card V - S.card = CN.card + (Comp.card - S.card) := by
                  intro S hS
                  have hSC : S.card ≤ Comp.card := card_le_card (mem_powerset.mp hS)
                  omega
                have hrew : ∀ S ∈ Comp.powerset,
                    p ^ S.card * (1 - p) ^ (Fintype.card V - S.card) =
                    (1 - p) ^ CN.card * (p ^ S.card * (1 - p) ^ (Comp.card - S.card)) := by
                  intro S hS; rw [hsub S hS, pow_add]; ring
                rw [Finset.sum_congr rfl hrew, ← Finset.mul_sum]
                have hbin := Finset.sum_pow_mul_eq_add_pow p (1 - p) Comp
                simp only [add_sub_cancel, one_pow] at hbin
                rw [hbin, mul_one]
                apply pow_le_pow_of_le_one (by linarith) (by linarith)
                rw [hCN_card]
                exact Nat.add_le_add_right (G.minDegree_le_degree v) 1

      _ = (n : ℝ) * (1 - p) ^ (δ + 1) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Theorem 3.1.1.** Every graph $G$ on $n$ vertices with minimum degree $\delta \geq 1$
has a dominating set of size at most $\frac{n(1 + \log(\delta + 1))}{\delta + 1}$. -/
theorem exists_dominating_set_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V]
    (hδ : 1 ≤ G.minDegree) :
    ∃ D : Finset V, IsDominatingSet G D ∧
      (D.card : ℝ) ≤ (Fintype.card V : ℝ) * (1 + Real.log ((G.minDegree : ℝ) + 1)) /
        ((G.minDegree : ℝ) + 1) := by
  classical
  set n := Fintype.card V
  set δ := G.minDegree
  set d : ℝ := (δ : ℝ) + 1
  have hd_pos : (0 : ℝ) < d := by positivity
  have hd_gt_one : (1 : ℝ) < d := by
    have : (1 : ℝ) ≤ (δ : ℝ) := Nat.one_le_cast.mpr hδ
    linarith
  set p : ℝ := Real.log d / d
  have hp_pos : 0 < p := div_pos (Real.log_pos hd_gt_one) hd_pos
  have hp_lt_one : p < 1 := by
    rw [div_lt_one hd_pos]
    linarith [Real.log_lt_sub_one_of_pos hd_pos (ne_of_gt hd_gt_one)]
  set bound : ℝ := (n : ℝ) * (1 + Real.log d) / d
  have h1mp_pow : (1 - p) ^ (δ + 1) ≤ 1 / d := by
    have h1 : 1 - p ≤ Real.exp (-p) := one_sub_le_exp_neg p
    have h2 : (Real.exp (-p)) ^ (δ + 1) = 1 / d := by
      rw [← Real.exp_nat_mul, show (↑(δ + 1) : ℝ) * (-p) = -Real.log d from by
        simp only [p]; push_cast; field_simp; ring]
      rw [Real.exp_neg, Real.exp_log hd_pos, one_div]
    calc (1 - p) ^ (δ + 1) ≤ (Real.exp (-p)) ^ (δ + 1) :=
          pow_le_pow_left₀ (by linarith) h1 _
      _ = 1 / d := h2
  suffices h : ∃ S : Finset V,
      (S.card : ℝ) + ((Finset.univ.filter fun v =>
        v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S).card : ℝ) ≤ bound from by
    obtain ⟨S, hS⟩ := h
    obtain ⟨D, hD_dom, hD_card⟩ := exists_dominating_from_subset G S hδ
    refine ⟨D, hD_dom, ?_⟩
    have : (D.card : ℝ) ≤ (S.card : ℝ) + ((Finset.univ.filter fun v =>
        v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S).card : ℝ) := by exact_mod_cast hD_card
    linarith
  let cost : Finset V → ℝ := fun S =>
    (S.card : ℝ) + ((Finset.univ.filter fun v =>
      v ∉ S ∧ ∀ u ∈ G.neighborFinset v, u ∉ S).card : ℝ)
  have havg : ∑ S ∈ (Finset.univ : Finset V).powerset, bernoulliWeight p S * cost S ≤
      bound := by
    have hexp := bernoulliWeight_expected_cost_le G p hp_pos hp_lt_one hδ
    have hbound : (n : ℝ) * p + (n : ℝ) * (1 - p) ^ (δ + 1) ≤ bound := by
      have h2_bound : (n : ℝ) * (1 - p) ^ (δ + 1) ≤ (n : ℝ) / d := by
        calc (n : ℝ) * (1 - p) ^ (δ + 1) ≤ (n : ℝ) * (1 / d) := by gcongr
          _ = (n : ℝ) / d := by ring
      have hbound_eq : (n : ℝ) * p + (n : ℝ) / d = bound := by
        simp only [bound, p, d]; field_simp; ring
      linarith
    linarith
  have htotal := bernoulliWeight_total (V := V) p
  by_contra h_no
  push_neg at h_no
  have hlt : bound < ∑ S ∈ (Finset.univ : Finset V).powerset,
      bernoulliWeight p S * cost S := by
    calc bound
        = bound * ∑ S ∈ (Finset.univ : Finset V).powerset, bernoulliWeight p S := by
          rw [htotal, mul_one]
      _ = ∑ S ∈ (Finset.univ : Finset V).powerset, bernoulliWeight p S * bound := by
          rw [Finset.mul_sum]; congr 1; ext S; ring
      _ < ∑ S ∈ (Finset.univ : Finset V).powerset, bernoulliWeight p S * cost S := by
          apply Finset.sum_lt_sum
          · intro S hS
            exact mul_le_mul_of_nonneg_left (le_of_lt (h_no S))
              (le_of_lt (mul_pos (pow_pos hp_pos _) (pow_pos (by linarith) _)))
          · refine ⟨(∅ : Finset V), Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩
            exact mul_lt_mul_of_pos_left (h_no (∅ : Finset V))
              (mul_pos (pow_pos hp_pos _) (pow_pos (by linarith : (0 : ℝ) < 1 - p) _))
  linarith

end DominatingSet
