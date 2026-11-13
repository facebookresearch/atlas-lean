/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Flow.FlowCutBound

open Finset BigOperators Classical

noncomputable section

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def resCap' (N : FlowNetwork V) (fl : STFlow N) (u v : V) : ℝ :=
  N.cap u v - fl.f u v + fl.f v u

def resAdj' (N : FlowNetwork V) (fl : STFlow N) (u v : V) : Prop :=
  resCap' N fl u v > 0

def ResReachable (N : FlowNetwork V) (fl : STFlow N) (v : V) : Prop :=
  Relation.ReflTransGen (resAdj' N fl) N.s v

def NoAugmentingPath (N : FlowNetwork V) (fl : STFlow N) : Prop :=
  ¬ ResReachable N fl N.t

lemma resCap'_nonneg (N : FlowNetwork V) (fl : STFlow N) (u v : V) :
    0 ≤ resCap' N fl u v := by
  unfold resCap'
  linarith [fl.flow_nonneg v u, fl.flow_cap u v]

lemma ResReachable_step {N : FlowNetwork V} {fl : STFlow N} {u v : V}
    (hu : ResReachable N fl u) (hadj : resAdj' N fl u v) :
    ResReachable N fl v :=
  hu.tail hadj

def resReachableSet (N : FlowNetwork V) (fl : STFlow N) : Finset V :=
  Finset.univ.filter (fun v => ResReachable N fl v)

lemma mem_resReachableSet_iff (N : FlowNetwork V) (fl : STFlow N) (v : V) :
    v ∈ resReachableSet N fl ↔ ResReachable N fl v := by
  simp [resReachableSet]

lemma s_mem_resReachableSet (N : FlowNetwork V) (fl : STFlow N) :
    N.s ∈ resReachableSet N fl := by
  rw [mem_resReachableSet_iff]
  exact Relation.ReflTransGen.refl

lemma t_not_mem_resReachableSet (N : FlowNetwork V) (fl : STFlow N) (hmax : NoAugmentingPath N fl) :
    N.t ∉ resReachableSet N fl := by
  rw [mem_resReachableSet_iff]
  exact hmax

def maxFlowCut (N : FlowNetwork V) (fl : STFlow N) (hmax : NoAugmentingPath N fl) :
    STCut N :=
  ⟨resReachableSet N fl, s_mem_resReachableSet N fl, t_not_mem_resReachableSet N fl hmax⟩

lemma maxFlowCut_S (N : FlowNetwork V) (fl : STFlow N) (hmax : NoAugmentingPath N fl) :
    (maxFlowCut N fl hmax).S = resReachableSet N fl := rfl

lemma not_resAdj_of_reach_nonreach {N : FlowNetwork V} {fl : STFlow N}
    {u v : V} (hu : ResReachable N fl u) (hv : ¬ ResReachable N fl v) :
    ¬ resAdj' N fl u v := by
  intro hadj
  exact hv (ResReachable_step hu hadj)

lemma resCap'_eq_zero_of_cross {N : FlowNetwork V} {fl : STFlow N}
    {u v : V} (hu : ResReachable N fl u) (hv : ¬ ResReachable N fl v) :
    resCap' N fl u v = 0 := by
  have hnadj := not_resAdj_of_reach_nonreach hu hv
  unfold resAdj' at hnadj
  have hge := resCap'_nonneg N fl u v
  linarith

lemma flow_eq_cap_of_cross {N : FlowNetwork V} {fl : STFlow N}
    {u v : V} (hu : ResReachable N fl u) (hv : ¬ ResReachable N fl v) :
    fl.f u v = N.cap u v := by
  have hrc := resCap'_eq_zero_of_cross hu hv
  unfold resCap' at hrc
  have hfv := fl.flow_nonneg v u
  have hfc := fl.flow_cap u v
  linarith

lemma flow_eq_zero_of_cross {N : FlowNetwork V} {fl : STFlow N}
    {u v : V} (hu : ResReachable N fl u) (hv : ¬ ResReachable N fl v) :
    fl.f v u = 0 := by
  have hrc := resCap'_eq_zero_of_cross hu hv
  unfold resCap' at hrc
  have hfc := fl.flow_cap u v
  have hfn := fl.flow_nonneg v u
  linarith

lemma flowValue_eq_cross (N : FlowNetwork V) (fl : STFlow N) (C : STCut N) :
    flowValue N fl =
      (∑ u ∈ C.S, ∑ v ∈ C.Sᶜ, fl.f u v) -
      (∑ u ∈ C.S, ∑ v ∈ C.Sᶜ, fl.f v u) := by
  unfold flowValue
  have hval : ∑ v : V, fl.f N.s v - ∑ v : V, fl.f v N.s =
      ∑ v ∈ C.S, (∑ w : V, fl.f v w - ∑ w : V, fl.f w v) := by
    have hcons : ∀ v ∈ C.S, v ≠ N.s →
        ∑ w : V, fl.f v w - ∑ w : V, fl.f w v = 0 := by
      intro v hv hvs
      have hvt : v ≠ N.t := fun h => C.t_not_mem (h ▸ hv)
      linarith [fl.conservation v hvs hvt]
    rw [← Finset.add_sum_erase C.S _ C.s_mem]
    simp only [Finset.sum_eq_zero (fun v hv => hcons v (Finset.mem_of_mem_erase hv)
      (Finset.ne_of_mem_erase hv)), add_zero]
  have hcross : ∑ v ∈ C.S, (∑ w : V, fl.f v w - ∑ w : V, fl.f w v) =
      (∑ v ∈ C.S, ∑ w ∈ C.Sᶜ, fl.f v w) -
      (∑ v ∈ C.S, ∑ w ∈ C.Sᶜ, fl.f w v) := by
    have split_out : ∀ v, ∑ w : V, fl.f v w =
        ∑ w ∈ C.S, fl.f v w + ∑ w ∈ C.Sᶜ, fl.f v w := by
      intro v; rw [← Finset.sum_add_sum_compl C.S]
    have split_in : ∀ v, ∑ w : V, fl.f w v =
        ∑ w ∈ C.S, fl.f w v + ∑ w ∈ C.Sᶜ, fl.f w v := by
      intro v; rw [← Finset.sum_add_sum_compl C.S]
    simp_rw [split_out, split_in]
    have cancel : ∑ v ∈ C.S, ∑ w ∈ C.S, fl.f v w =
        ∑ v ∈ C.S, ∑ w ∈ C.S, fl.f w v := by
      rw [Finset.sum_comm]
    have h1 : ∑ v ∈ C.S, (∑ w ∈ C.S, fl.f v w + ∑ w ∈ C.Sᶜ, fl.f v w -
        (∑ w ∈ C.S, fl.f w v + ∑ w ∈ C.Sᶜ, fl.f w v)) =
      (∑ v ∈ C.S, ∑ w ∈ C.S, fl.f v w) + (∑ v ∈ C.S, ∑ w ∈ C.Sᶜ, fl.f v w) -
      (∑ v ∈ C.S, ∑ w ∈ C.S, fl.f w v) - (∑ v ∈ C.S, ∑ w ∈ C.Sᶜ, fl.f w v) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
    linarith
  linarith

theorem max_flow_min_cut (N : FlowNetwork V) (fl : STFlow N) (hmax : NoAugmentingPath N fl) :
    ∃ C : STCut N, flowValue N fl = cutCapacity N C := by
  use maxFlowCut N fl hmax
  have heq := flowValue_eq_cross N fl (maxFlowCut N fl hmax)
  rw [heq]

  have hfwd : ∑ u ∈ (maxFlowCut N fl hmax).S, ∑ v ∈ (maxFlowCut N fl hmax).Sᶜ, fl.f u v =
      cutCapacity N (maxFlowCut N fl hmax) := by
    unfold cutCapacity
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    have hu_reach : ResReachable N fl u := by
      rw [maxFlowCut_S] at hu
      exact (mem_resReachableSet_iff N fl u).mp hu
    have hv_not_reach : ¬ ResReachable N fl v := by
      rw [maxFlowCut_S] at hv
      rw [Finset.mem_compl] at hv
      exact fun h => hv ((mem_resReachableSet_iff N fl v).mpr h)
    exact flow_eq_cap_of_cross hu_reach hv_not_reach

  have hbwd : ∑ u ∈ (maxFlowCut N fl hmax).S, ∑ v ∈ (maxFlowCut N fl hmax).Sᶜ, fl.f v u = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro v hv
    have hu_reach : ResReachable N fl u := by
      rw [maxFlowCut_S] at hu
      exact (mem_resReachableSet_iff N fl u).mp hu
    have hv_not_reach : ¬ ResReachable N fl v := by
      rw [maxFlowCut_S] at hv
      rw [Finset.mem_compl] at hv
      exact fun h => hv ((mem_resReachableSet_iff N fl v).mpr h)
    exact flow_eq_zero_of_cross hu_reach hv_not_reach
  linarith

end NetworkFlow
