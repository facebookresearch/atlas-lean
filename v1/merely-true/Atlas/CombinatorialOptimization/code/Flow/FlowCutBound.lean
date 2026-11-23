/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset BigOperators

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

structure FlowNetwork (V : Type*) [Fintype V] [DecidableEq V] where
  cap : V → V → ℝ
  s : V
  t : V
  s_ne_t : s ≠ t
  cap_nonneg : ∀ u v, 0 ≤ cap u v

structure STFlow (N : FlowNetwork V) where
  f : V → V → ℝ
  flow_nonneg : ∀ u v, 0 ≤ f u v
  flow_cap : ∀ u v, f u v ≤ N.cap u v
  conservation : ∀ v, v ≠ N.s → v ≠ N.t →
    ∑ u : V, f u v = ∑ u : V, f v u

noncomputable def flowValue (N : FlowNetwork V) (fl : STFlow N) : ℝ :=
  ∑ v : V, fl.f N.s v - ∑ v : V, fl.f v N.s

structure STCut (N : FlowNetwork V) where
  S : Finset V
  s_mem : N.s ∈ S
  t_not_mem : N.t ∉ S

noncomputable def cutCapacity (N : FlowNetwork V) (C : STCut N) : ℝ :=
  ∑ u ∈ C.S, ∑ v ∈ C.Sᶜ, N.cap u v

theorem flow_le_cut (N : FlowNetwork V) (fl : STFlow N) (C : STCut N) :
    flowValue N fl ≤ cutCapacity N C := by


  have hval : flowValue N fl =
      ∑ v ∈ C.S, (∑ w : V, fl.f v w - ∑ w : V, fl.f w v) := by
    unfold flowValue
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

  rw [hval, hcross]
  have h_nonneg_back : 0 ≤ ∑ v ∈ C.S, ∑ w ∈ C.Sᶜ, fl.f w v := by
    apply Finset.sum_nonneg
    intro v _
    apply Finset.sum_nonneg
    intro w _
    exact fl.flow_nonneg w v
  have h_flow_le_cap : ∑ v ∈ C.S, ∑ w ∈ C.Sᶜ, fl.f v w ≤ cutCapacity N C := by
    unfold cutCapacity
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    exact fl.flow_cap u v
  linarith

end NetworkFlow
