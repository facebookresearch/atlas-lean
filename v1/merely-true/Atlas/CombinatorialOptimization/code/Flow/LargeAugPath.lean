/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Flow.FlowDecomposition
import Atlas.CombinatorialOptimization.code.Flow.ResidualGraph

open Finset BigOperators Classical

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsMaxFlow (N : FlowNetwork V) (fl : STFlow N) : Prop :=
  ∀ fl' : STFlow N, flowValue N fl' ≤ flowValue N fl

noncomputable def edgeCount (N : FlowNetwork V) : ℕ :=
  (Finset.univ.filter (fun e : V × V => N.cap e.1 e.2 > 0)).card

lemma max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  by_cases h : a ≤ 0
  · have hna : (0 : ℝ) ≤ -a := by linarith
    rw [max_eq_right h, max_eq_left hna]
    ring
  · push_neg at h
    have hna : -a ≤ (0 : ℝ) := by linarith
    rw [max_eq_left (le_of_lt h), max_eq_right hna]
    ring

noncomputable def residualNetwork (N : FlowNetwork V) (fl : STFlow N) : FlowNetwork V :=
  { s := N.s
    t := N.t
    s_ne_t := N.s_ne_t
    cap := fun u v => resCap N fl u v
    cap_nonneg := fun u v => resCap_nonneg N fl u v }

noncomputable def diffFlowFun (N : FlowNetwork V) (fl fl_max : STFlow N) (u v : V) : ℝ :=
  max (fl_max.f u v - fl.f u v) 0 + max (fl.f v u - fl_max.f v u) 0

lemma diffFlowFun_nonneg (N : FlowNetwork V) (fl fl_max : STFlow N) (u v : V) :
    0 ≤ diffFlowFun N fl fl_max u v := by
  unfold diffFlowFun; positivity

lemma diffFlowFun_le_resCap (N : FlowNetwork V) (fl fl_max : STFlow N) (u v : V) :
    diffFlowFun N fl fl_max u v ≤ resCap N fl u v := by
  unfold diffFlowFun resCap
  have h1 := fl_max.flow_cap u v
  have h2 := fl_max.flow_nonneg v u
  have h3 := fl.flow_nonneg u v
  have h4 := fl.flow_cap v u
  have h5 := fl.flow_cap u v
  have h6 := fl.flow_nonneg v u
  have hle1 : max (fl_max.f u v - fl.f u v) 0 ≤ N.cap u v - fl.f u v := by
    apply max_le <;> linarith
  have hle2 : max (fl.f v u - fl_max.f v u) 0 ≤ fl.f v u := by
    apply max_le <;> linarith
  linarith

lemma diffFlowFun_conservation (N : FlowNetwork V) (fl fl_max : STFlow N) (w : V)
    (hw_s : w ≠ N.s) (hw_t : w ≠ N.t) :
    ∑ u : V, diffFlowFun N fl fl_max u w = ∑ u : V, diffFlowFun N fl fl_max w u := by
  suffices h : ∑ u : V, diffFlowFun N fl fl_max u w -
      ∑ u : V, diffFlowFun N fl fl_max w u = 0 by linarith
  simp only [diffFlowFun]
  rw [show ∑ u : V, (max (fl_max.f u w - fl.f u w) 0 + max (fl.f w u - fl_max.f w u) 0) =
      ∑ u : V, max (fl_max.f u w - fl.f u w) 0 + ∑ u : V, max (fl.f w u - fl_max.f w u) 0
    from Finset.sum_add_distrib]
  rw [show ∑ u : V, (max (fl_max.f w u - fl.f w u) 0 + max (fl.f u w - fl_max.f u w) 0) =
      ∑ u : V, max (fl_max.f w u - fl.f w u) 0 + ∑ u : V, max (fl.f u w - fl_max.f u w) 0
    from Finset.sum_add_distrib]
  have eq1 : ∑ u : V, max (fl_max.f u w - fl.f u w) 0 -
             ∑ u : V, max (fl.f u w - fl_max.f u w) 0 =
             ∑ u : V, (fl_max.f u w - fl.f u w) := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext u
    have h2 : fl.f u w - fl_max.f u w = -(fl_max.f u w - fl.f u w) := by ring
    rw [h2]
    exact max_sub_max_neg (fl_max.f u w - fl.f u w)
  have eq2 : ∑ u : V, max (fl.f w u - fl_max.f w u) 0 -
             ∑ u : V, max (fl_max.f w u - fl.f w u) 0 =
             ∑ u : V, (fl.f w u - fl_max.f w u) := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext u
    have h2 : fl_max.f w u - fl.f w u = -(fl.f w u - fl_max.f w u) := by ring
    rw [h2]
    exact max_sub_max_neg (fl.f w u - fl_max.f w u)

  have cons_max := fl_max.conservation w hw_s hw_t
  have cons_fl := fl.conservation w hw_s hw_t
  linarith [Finset.sum_sub_distrib (s := Finset.univ)
              (f := fun u => fl_max.f u w) (g := fun u => fl.f u w),
            Finset.sum_sub_distrib (s := Finset.univ)
              (f := fun u => fl.f w u) (g := fun u => fl_max.f w u)]

noncomputable def diffFlow (N : FlowNetwork V) (fl fl_max : STFlow N) :
    STFlow (residualNetwork N fl) :=
  { f := diffFlowFun N fl fl_max
    flow_nonneg := diffFlowFun_nonneg N fl fl_max
    flow_cap := diffFlowFun_le_resCap N fl fl_max
    conservation := diffFlowFun_conservation N fl fl_max }

lemma diffFlow_value (N : FlowNetwork V) (fl fl_max : STFlow N) :
    flowValue (residualNetwork N fl) (diffFlow N fl fl_max) =
    flowValue N fl_max - flowValue N fl := by
  unfold flowValue residualNetwork diffFlow diffFlowFun
  simp only
  rw [show ∑ v : V, (max (fl_max.f N.s v - fl.f N.s v) 0 + max (fl.f v N.s - fl_max.f v N.s) 0) =
      ∑ v : V, max (fl_max.f N.s v - fl.f N.s v) 0 + ∑ v : V, max (fl.f v N.s - fl_max.f v N.s) 0
    from Finset.sum_add_distrib]
  rw [show ∑ v : V, (max (fl_max.f v N.s - fl.f v N.s) 0 + max (fl.f N.s v - fl_max.f N.s v) 0) =
      ∑ v : V, max (fl_max.f v N.s - fl.f v N.s) 0 + ∑ v : V, max (fl.f N.s v - fl_max.f N.s v) 0
    from Finset.sum_add_distrib]
  have eq1 : ∑ v : V, max (fl_max.f N.s v - fl.f N.s v) 0 -
             ∑ v : V, max (fl.f N.s v - fl_max.f N.s v) 0 =
             ∑ v : V, (fl_max.f N.s v - fl.f N.s v) := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext u
    have h2 : fl.f N.s u - fl_max.f N.s u = -(fl_max.f N.s u - fl.f N.s u) := by ring
    rw [h2]
    exact max_sub_max_neg (fl_max.f N.s u - fl.f N.s u)
  have eq2 : ∑ v : V, max (fl.f v N.s - fl_max.f v N.s) 0 -
             ∑ v : V, max (fl_max.f v N.s - fl.f v N.s) 0 =
             ∑ v : V, (fl.f v N.s - fl_max.f v N.s) := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext u
    have h2 : fl_max.f u N.s - fl.f u N.s = -(fl.f u N.s - fl_max.f u N.s) := by ring
    rw [h2]
    exact max_sub_max_neg (fl.f u N.s - fl_max.f u N.s)

  linarith [Finset.sum_sub_distrib (s := Finset.univ)
              (f := fun v => fl_max.f N.s v) (g := fun v => fl.f N.s v),
            Finset.sum_sub_distrib (s := Finset.univ)
              (f := fun v => fl.f v N.s) (g := fun v => fl_max.f v N.s)]

lemma diffFlow_support_le_edgeCount (N : FlowNetwork V) (fl fl_max : STFlow N) :
    (flowSupport (residualNetwork N fl) (diffFlow N fl fl_max)).card ≤ edgeCount N := by
  unfold flowSupport edgeCount

  let φ : V × V → V × V := fun e => if N.cap e.1 e.2 > 0 then e else (e.2, e.1)
  apply Finset.card_le_card_of_injOn φ
  ·
    intro e he
    simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
               true_and, Set.mem_setOf_eq] at he ⊢
    simp only [φ]
    split_ifs with h
    · exact h
    ·
      push_neg at h
      have hcap0 : N.cap e.1 e.2 = 0 := le_antisymm h (N.cap_nonneg e.1 e.2)

      have hdf : (diffFlow N fl fl_max).f e.1 e.2 > 0 := he
      have hrc := diffFlowFun_le_resCap N fl fl_max e.1 e.2
      simp only [diffFlow, resCap] at hdf hrc

      have hf0 : fl.f e.1 e.2 = 0 := le_antisymm (by linarith [fl.flow_cap e.1 e.2]) (fl.flow_nonneg e.1 e.2)

      linarith [fl.flow_cap e.2 e.1, fl.flow_nonneg e.2 e.1]
  ·
    intro e₁ he₁ e₂ he₂ heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
               Finset.mem_univ, true_and] at he₁ he₂
    simp only [φ] at heq
    split_ifs at heq with h1 h2 h2
    · exact heq
    ·
      exfalso
      push_neg at h2
      have hcap0 : N.cap e₂.1 e₂.2 = 0 := le_antisymm h2 (N.cap_nonneg e₂.1 e₂.2)

      have heq12 : e₁ = (e₂.2, e₂.1) := heq

      have hdf2 : (diffFlow N fl fl_max).f e₂.1 e₂.2 > 0 := he₂
      simp only [diffFlow, diffFlowFun] at hdf2
      have hfm0 : fl_max.f e₂.1 e₂.2 = 0 := le_antisymm (by linarith [fl_max.flow_cap e₂.1 e₂.2]) (fl_max.flow_nonneg e₂.1 e₂.2)
      have hfl0 : fl.f e₂.1 e₂.2 = 0 := le_antisymm (by linarith [fl.flow_cap e₂.1 e₂.2]) (fl.flow_nonneg e₂.1 e₂.2)
      simp only [hfm0, hfl0, sub_zero, le_refl, max_eq_right] at hdf2

      have hgt : fl.f e₂.2 e₂.1 > fl_max.f e₂.2 e₂.1 := by
        by_contra h; push_neg at h
        have := max_eq_right (show fl.f e₂.2 e₂.1 - fl_max.f e₂.2 e₂.1 ≤ 0 from by linarith)
        linarith


      have hdf1 : (diffFlow N fl fl_max).f e₁.1 e₁.2 > 0 := he₁
      rw [heq12] at hdf1
      simp only [diffFlow, diffFlowFun] at hdf1
      simp only [hfl0, hfm0, sub_zero, le_refl, max_eq_right] at hdf1


      have hgt2 : fl_max.f e₂.2 e₂.1 > fl.f e₂.2 e₂.1 := by
        by_contra h; push_neg at h
        have := max_eq_right (show fl_max.f e₂.2 e₂.1 - fl.f e₂.2 e₂.1 ≤ 0 from by linarith)
        linarith
      linarith
    ·
      exfalso
      push_neg at h1
      have hcap0 : N.cap e₁.1 e₁.2 = 0 := le_antisymm h1 (N.cap_nonneg e₁.1 e₁.2)
      have heq12 : e₂ = (e₁.2, e₁.1) := heq.symm
      have hdf1 : (diffFlow N fl fl_max).f e₁.1 e₁.2 > 0 := he₁
      simp only [diffFlow, diffFlowFun] at hdf1
      have hfm0 : fl_max.f e₁.1 e₁.2 = 0 := le_antisymm (by linarith [fl_max.flow_cap e₁.1 e₁.2]) (fl_max.flow_nonneg e₁.1 e₁.2)
      have hfl0 : fl.f e₁.1 e₁.2 = 0 := le_antisymm (by linarith [fl.flow_cap e₁.1 e₁.2]) (fl.flow_nonneg e₁.1 e₁.2)
      simp only [hfm0, hfl0, sub_zero, le_refl, max_eq_right] at hdf1
      have hgt : fl.f e₁.2 e₁.1 > fl_max.f e₁.2 e₁.1 := by
        by_contra h; push_neg at h
        have := max_eq_right (show fl.f e₁.2 e₁.1 - fl_max.f e₁.2 e₁.1 ≤ 0 from by linarith)
        linarith
      have hdf2 : (diffFlow N fl fl_max).f e₂.1 e₂.2 > 0 := he₂
      rw [heq12] at hdf2
      simp only [diffFlow, diffFlowFun] at hdf2
      simp only [hfl0, hfm0, sub_zero, le_refl, max_eq_right] at hdf2
      have hgt2 : fl_max.f e₁.2 e₁.1 > fl.f e₁.2 e₁.1 := by
        by_contra h; push_neg at h
        have := max_eq_right (show fl_max.f e₁.2 e₁.1 - fl.f e₁.2 e₁.1 ≤ 0 from by linarith)
        linarith
      linarith
    ·
      exact Prod.ext (Prod.mk.inj heq).2 (Prod.mk.inj heq).1


lemma FlowPath.consecutive_mem_edges {N' : FlowNetwork V} (p : FlowPath N')
    (idx : ℕ) (hidx : idx + 1 < p.vertices.length) :
    p.mem_edges (p.vertices[idx]'(by omega)) (p.vertices[idx + 1]'hidx) := by
  unfold FlowPath.mem_edges FlowPath.edges
  have hlen : idx < (p.vertices.zip p.vertices.tail).length := by
    simp [List.length_zip, List.length_tail]; omega
  have heq : (p.vertices.zip p.vertices.tail)[idx]'hlen =
      (p.vertices[idx]'(by omega), p.vertices[idx + 1]'hidx) := by
    rw [List.getElem_zip]
    congr 1
    rw [List.getElem_tail]
  exact heq ▸ List.getElem_mem hlen

lemma FlowDecomposition.sum_ge_weight {N' : FlowNetwork V} {fl' : STFlow N'}
    (decomp : FlowDecomposition N' fl') (i : Fin decomp.k) (u v : V)
    (hmem : (decomp.paths i).mem_edges u v) :
    decomp.weights i ≤ ∑ j : Fin decomp.k,
      if (decomp.paths j).mem_edges u v then decomp.weights j else 0 := by
  have h_nonneg : ∀ j ∈ Finset.univ, (0 : ℝ) ≤
      if (decomp.paths j).mem_edges u v then decomp.weights j else 0 := by
    intro j _
    by_cases hj : (decomp.paths j).mem_edges u v
    · rw [if_pos hj]; exact le_of_lt (decomp.weights_pos j)
    · rw [if_neg hj]
  have h_eq : (if (decomp.paths i).mem_edges u v then decomp.weights i else 0) =
      decomp.weights i := if_pos hmem
  calc decomp.weights i = if (decomp.paths i).mem_edges u v then decomp.weights i else 0 :=
        h_eq.symm
    _ ≤ ∑ j : Fin decomp.k,
        if (decomp.paths j).mem_edges u v then decomp.weights j else 0 :=
      Finset.single_le_sum h_nonneg (Finset.mem_univ i)

lemma flowPath_to_augmenting (N : FlowNetwork V) (fl fl_max : STFlow N)
    (decomp : FlowDecomposition (residualNetwork N fl) (diffFlow N fl fl_max))
    (i : Fin decomp.k) :
    IsAugmentingPath N fl (decomp.paths i).vertices := by
  unfold IsAugmentingPath IsDirectedPath
  set p := decomp.paths i
  refine ⟨p.length_ge_two, ?_, ?_, p.nodup, ?_⟩
  · rw [List.head?_eq_head p.nonempty]
    exact congrArg some p.starts_at_s
  · rw [List.getLast?_eq_getLast p.nonempty]
    exact congrArg some p.ends_at_t
  · intro idx hidx
    unfold resAdj


    have hflow_pos : decomp.f'.f
        (p.vertices.get ⟨idx, by omega⟩)
        (p.vertices.get ⟨idx + 1, hidx⟩) > 0 := by
      have hfe := decomp.flow_eq
          (p.vertices.get ⟨idx, by omega⟩) (p.vertices.get ⟨idx + 1, hidx⟩)
      rw [hfe]
      have hmem := FlowPath.consecutive_mem_edges p idx hidx
      exact lt_of_lt_of_le (decomp.weights_pos i) (decomp.sum_ge_weight i _ _ hmem)

    have hcap := decomp.f'.flow_cap
        (p.vertices.get ⟨idx, by omega⟩) (p.vertices.get ⟨idx + 1, hidx⟩)

    have hcap_eq : (residualNetwork N fl).cap (p.vertices.get ⟨idx, by omega⟩)
        (p.vertices.get ⟨idx + 1, hidx⟩) = resCap N fl (p.vertices.get ⟨idx, by omega⟩)
        (p.vertices.get ⟨idx + 1, hidx⟩) := rfl
    linarith



end NetworkFlow
