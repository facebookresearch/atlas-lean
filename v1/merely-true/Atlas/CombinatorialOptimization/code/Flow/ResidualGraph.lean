/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Flow.FlowCutBound

open Finset BigOperators

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def resCap (N : FlowNetwork V) (fl : STFlow N) (u v : V) : ℝ :=
  N.cap u v - fl.f u v + fl.f v u

def resAdj (N : FlowNetwork V) (fl : STFlow N) (u v : V) : Prop :=
  resCap N fl u v > 0

lemma resCap_nonneg (N : FlowNetwork V) (fl : STFlow N) (u v : V) :
    0 ≤ resCap N fl u v := by
  unfold resCap
  linarith [fl.flow_nonneg v u, fl.flow_cap u v]

lemma resAdj_iff (N : FlowNetwork V) (fl : STFlow N) (u v : V) :
    resAdj N fl u v ↔ (N.cap u v - fl.f u v > 0 ∨ fl.f v u > 0) := by
  unfold resAdj resCap
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    linarith [hc.1, hc.2, fl.flow_cap u v, fl.flow_nonneg v u]
  · intro h
    cases h with
    | inl h => linarith [fl.flow_nonneg v u]
    | inr h => linarith [fl.flow_cap u v, N.cap_nonneg u v]

def IsDirectedPath (adj : V → V → Prop) (s t : V) (p : List V) : Prop :=
  p.length ≥ 2 ∧
  p.head? = some s ∧
  p.getLast? = some t ∧
  p.Nodup ∧
  (∀ i : ℕ, (hi : i + 1 < p.length) →
    adj (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, hi⟩))

def IsOriginalAugmentingPath (N : FlowNetwork V) (fl : STFlow N)
    (p : List V) : Prop :=
  p.head? = some N.s ∧ p.getLast? = some N.t ∧ p.length ≥ 2 ∧
  p.Chain' (fun u v => N.cap u v - fl.f u v > 0 ∨ fl.f v u > 0) ∧
  p.Nodup

def IsAugmentingPath (N : FlowNetwork V) (fl : STFlow N) (p : List V) : Prop :=
  IsDirectedPath (resAdj N fl) N.s N.t p

theorem augmentingPath_iff_residualPath' (N : FlowNetwork V) (fl : STFlow N)
    (p : List V) :
    IsOriginalAugmentingPath N fl p ↔ IsDirectedPath (resAdj N fl) N.s N.t p := by
  unfold IsOriginalAugmentingPath IsDirectedPath
  have chain_iff : p.Chain' (fun u v => N.cap u v - fl.f u v > 0 ∨ fl.f v u > 0) ↔
      (∀ i : ℕ, (hi : i + 1 < p.length) →
        resAdj N fl (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, hi⟩)) := by
    rw [show p.Chain' _ = p.IsChain _ from rfl, List.isChain_iff_getElem]
    constructor
    · intro h i hi
      rw [resAdj_iff]
      exact h i hi
    · intro h i hi
      rw [← resAdj_iff]
      exact h i hi
  constructor
  · rintro ⟨hhead, hlast, hlen, hchain, hnodup⟩
    exact ⟨hlen, hhead, hlast, hnodup, chain_iff.mp hchain⟩
  · rintro ⟨hlen, hhead, hlast, hnodup, hadj⟩
    exact ⟨hhead, hlast, hlen, chain_iff.mpr hadj, hnodup⟩

noncomputable def pathBottleneck (N : FlowNetwork V) (fl : STFlow N) (p : List V)
    (hp : p.length ≥ 2) : ℝ :=
  (Finset.range (p.length - 1)).inf' (by rw [Finset.nonempty_range_iff]; omega)
    (fun i => if h : i + 1 < p.length
      then resCap N fl (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, h⟩)
      else 0)

end NetworkFlow
