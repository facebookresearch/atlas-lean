/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Flow.ResidualGraph

open Finset BigOperators

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def dirPathLengths (adj : V → V → Prop) (s t : V) : Set ℕ∞ :=
  { n : ℕ∞ | ∃ (k : ℕ) (p : List V), IsDirectedPath adj s t p ∧
    p.length = k + 1 ∧ n = ↑k }

noncomputable def dirDist (adj : V → V → Prop) (s t : V) : ℕ∞ :=
  sInf (dirPathLengths adj s t)

noncomputable def residualDist (N : FlowNetwork V) (fl : STFlow N) : ℕ∞ :=
  dirDist (resAdj N fl) N.s N.t

def EdgeOnPath (path : List V) (u v : V) : Prop :=
  ∃ i : ℕ, path[i]? = some u ∧ path[i + 1]? = some v

def IsShortestAugmentingPath (N : FlowNetwork V) (fl : STFlow N)
    (p : List V) : Prop :=
  IsAugmentingPath N fl p ∧
  (↑(p.length - 1) : ℕ∞) = residualDist N fl

def IsShortestPathAugmentation (N : FlowNetwork V) (fl fl' : STFlow N) : Prop :=
  ∃ p : List V,
    IsShortestAugmentingPath N fl p ∧
    (∑ v : V, fl'.f N.s v - ∑ v : V, fl'.f v N.s) >
    (∑ v : V, fl.f N.s v - ∑ v : V, fl.f v N.s) ∧
    (∀ u v, ¬ EdgeOnPath p u v → ¬ EdgeOnPath p v u → fl'.f u v = fl.f u v) ∧
    (∀ (q : List V) (hq : IsShortestAugmentingPath N fl q) (u v : V),
      EdgeOnPath q u v → resCap N fl u v = pathBottleneck N fl q hq.1.1 →
      ¬ resAdj N fl' u v)

lemma dirDist_le_of_path {adj : V → V → Prop} {s t : V} {p : List V}
    (hp : IsDirectedPath adj s t p) :
    dirDist adj s t ≤ ↑(p.length - 1) := by
  unfold dirDist
  apply sInf_le
  simp only [dirPathLengths, Set.mem_setOf_eq]
  refine ⟨p.length - 1, p, hp, ?_, rfl⟩
  have := hp.1
  omega

lemma isDirectedPath_take {adj : V → V → Prop} {s t : V} {p : List V}
    (hp : IsDirectedPath adj s t p) (j : ℕ) (hj : 1 ≤ j) (hj2 : j + 1 ≤ p.length) :
    IsDirectedPath adj s (p.get ⟨j, by omega⟩) (p.take (j + 1)) := by
  obtain ⟨hlen, hhead, hlast, hnodup, hadj⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [List.length_take]; omega
  · rw [List.head?_take]; simp [show j + 1 ≠ 0 from by omega, hhead]
  · rw [List.getLast?_eq_getElem?]
    simp only [List.length_take, show min (j + 1) p.length = j + 1 from by omega]
    rw [show j + 1 - 1 = j from by omega]
    simp only [List.getElem?_take, show j < j + 1 from by omega, ite_true]
    exact List.getElem?_eq_getElem (by omega)
  · exact hnodup.sublist (List.take_sublist _ _)
  · intro i hi
    have hi_lt_j1 : i + 1 < j + 1 := by simp [List.length_take] at hi; omega
    have hilen : i + 1 < p.length := by omega
    have hget1 : (p.take (j + 1)).get ⟨i, by simp [List.length_take]; omega⟩ =
        p.get ⟨i, by omega⟩ := by
      simp only [List.get_eq_getElem]
      exact (List.getElem_take' (show i < p.length from by omega)
        (show i < j + 1 from by omega)).symm
    have hget2 : (p.take (j + 1)).get ⟨i + 1, hi⟩ =
        p.get ⟨i + 1, hilen⟩ := by
      simp only [List.get_eq_getElem]
      exact (List.getElem_take' hilen hi_lt_j1).symm
    rw [hget1, hget2]
    exact hadj i hilen

lemma new_edge_on_reverse_path
    (N : FlowNetwork V) (fl fl' : STFlow N)
    (p : List V) (hp_aug : IsAugmentingPath N fl p)
    (hflow_change : ∀ u v, ¬ EdgeOnPath p u v → ¬ EdgeOnPath p v u → fl'.f u v = fl.f u v)
    {u v : V} (hnew : resAdj N fl' u v) (hold : ¬ resAdj N fl u v) :
    EdgeOnPath p v u := by


  by_contra h_not_vu
  by_cases h_uv : EdgeOnPath p u v
  ·

    obtain ⟨i, hi_u, hi_v⟩ := h_uv
    have hp_dir := hp_aug
    unfold IsAugmentingPath at hp_dir
    obtain ⟨_, _, _, _, hadj⟩ := hp_dir
    have hi_bound : i + 1 < p.length := by
      have := List.getElem?_eq_some_iff.mp hi_v
      exact this.1
    have hu_eq : p.get ⟨i, by omega⟩ = u := by
      have := (List.getElem?_eq_some_iff.mp hi_u).2
      simp [List.get_eq_getElem] at this ⊢; exact this
    have hv_eq : p.get ⟨i + 1, hi_bound⟩ = v := by
      have := (List.getElem?_eq_some_iff.mp hi_v).2
      simp [List.get_eq_getElem] at this ⊢; exact this
    have := hadj i hi_bound
    rw [hu_eq, hv_eq] at this
    exact hold this
  ·
    have hf_uv : fl'.f u v = fl.f u v := hflow_change u v h_uv h_not_vu
    have hf_vu : fl'.f v u = fl.f v u := by
      apply hflow_change
      · exact h_not_vu
      · exact h_uv

    unfold resAdj resCap at hnew hold
    linarith

lemma getElem_take_append_drop {w : List V} {i j k : Nat}
    (hij : i < j) (hj_lt : j < w.length)
    (hk : k < (w.take (i + 1) ++ w.drop (j + 1)).length) :
    (w.take (i + 1) ++ w.drop (j + 1))[k] =
    if k ≤ i then w[k]'(by
      have : (w.take (i + 1) ++ w.drop (j + 1)).length = w.length - (j - i) := by
        simp [List.length_take, List.length_drop]; omega
      omega)
    else w[k + (j - i)]'(by
      have : (w.take (i + 1) ++ w.drop (j + 1)).length = w.length - (j - i) := by
        simp [List.length_take, List.length_drop]; omega
      omega) := by
  have h_take_len : (w.take (i + 1)).length = i + 1 := by
    simp [List.length_take]; omega
  split_ifs with hki
  · rw [List.getElem_append_left (by rw [h_take_len]; omega)]; exact List.getElem_take
  · have h_ge : (w.take (i + 1)).length ≤ k := by rw [h_take_len]; omega
    rw [List.getElem_append_right h_ge]
    simp only [List.getElem_drop, h_take_len]; congr 1; omega

lemma eq_of_getElem?_eq (w : List V) (i j : Nat) (hi : i < w.length) (hj : j < w.length)
    (h : w[i]? = w[j]?) : w[i] = w[j] := by
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at h
  exact Option.some_injective _ h

lemma walk_to_simple_path {adj : V → V → Prop} {s t : V} (w : List V)
    (hlen : w.length ≥ 2)
    (hhead : w.head? = some s)
    (hlast : w.getLast? = some t)
    (hadj : ∀ i : ℕ, (hi : i + 1 < w.length) →
      adj (w.get ⟨i, by omega⟩) (w.get ⟨i + 1, hi⟩))
    (hst : s ≠ t) :
    ∃ q : List V, IsDirectedPath adj s t q ∧ q.length ≤ w.length := by
  suffices ∀ (n : ℕ) (w : List V), w.length = n → w.length ≥ 2 →
      w.head? = some s → w.getLast? = some t →
      (∀ i : ℕ, (hi : i + 1 < w.length) → adj (w.get ⟨i, by omega⟩) (w.get ⟨i + 1, hi⟩)) →
      ∃ q : List V, IsDirectedPath adj s t q ∧ q.length ≤ w.length by
    exact this w.length w rfl hlen hhead hlast hadj
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro w hw_len hlen' hhead' hlast' hadj'
    by_cases hnodup : w.Nodup
    · exact ⟨w, ⟨hlen', hhead', hlast', hnodup, hadj'⟩, le_refl _⟩
    · rw [List.nodup_iff_getElem?_ne_getElem?] at hnodup
      push_neg at hnodup
      obtain ⟨i, j, hij, hj_lt, heq⟩ := hnodup
      have hi_lt : i < w.length := Nat.lt_trans hij hj_lt
      have h_eq : w[i] = w[j] := eq_of_getElem?_eq w i j hi_lt hj_lt heq
      set w' := w.take (i + 1) ++ w.drop (j + 1)
      have hw'_len : w'.length = w.length - (j - i) := by
        simp [w', List.length_take, List.length_drop]; omega
      have hw'_lt : w'.length < n := by omega
      have hw'_head : w'.head? = some s := by
        simp [w', List.head?_append, List.head?_take, hhead', Option.some_or]
      have hw'_last : w'.getLast? = some t := by
        simp only [w', List.getLast?_append, List.getLast?_drop]
        by_cases hj1 : w.length ≤ j + 1
        · simp only [hj1, ite_true, Option.none_or]
          rw [List.getLast?_eq_getElem?]
          simp only [List.length_take, show min (i + 1) w.length = i + 1 from by omega,
            show i + 1 - 1 = i from by omega]
          rw [show (List.take (i + 1) w)[i]? = w[i]? from by
            simp [show i < i + 1 from by omega]]
          rw [List.getElem?_eq_getElem hi_lt]; congr 1; rw [h_eq]
          rw [List.getLast?_eq_getElem?] at hlast'
          have htj : w[j]? = some t := by convert hlast' using 2; omega
          rw [List.getElem?_eq_getElem hj_lt] at htj
          exact (Option.some_injective _ htj)
        · push_neg at hj1
          simp only [show ¬ (w.length ≤ j + 1) from by omega, ite_false, hlast', Option.some_or]
      have hw'_len2 : w'.length ≥ 2 := by
        by_contra h_lt2; push_neg at h_lt2
        have h1 : w'.length ≥ 1 := by rw [hw'_len]; omega
        have : w'.length = 1 := by omega
        have heq' : w'.head? = w'.getLast? := by
          rw [List.head?_eq_getElem?, List.getLast?_eq_getElem?]; congr 1; omega
        rw [hw'_head, hw'_last] at heq'
        exact hst (Option.some_injective _ heq')
      have hw'_adj : ∀ k : ℕ, (hk : k + 1 < w'.length) →
          adj (w'.get ⟨k, by omega⟩) (w'.get ⟨k + 1, hk⟩) := by
        intro k hk
        have hk_bound : k + 1 < w.length - (j - i) := by rw [← hw'_len]; exact hk
        have hk_lt_w' : k < w'.length := by omega
        have hk1_lt_w' : k + 1 < w'.length := hk
        simp only [List.get_eq_getElem]
        have hk_lt_concat : k < (w.take (i + 1) ++ w.drop (j + 1)).length := by
          change k < w'.length; exact hk_lt_w'
        have hk1_lt_concat : k + 1 < (w.take (i + 1) ++ w.drop (j + 1)).length := by
          change k + 1 < w'.length; exact hk1_lt_w'
        rw [getElem_take_append_drop hij hj_lt hk_lt_concat]
        rw [getElem_take_append_drop hij hj_lt hk1_lt_concat]
        split_ifs with h1 h2 h2
        · have := hadj' k (by omega)
          simpa [List.get_eq_getElem] using this
        · have hk_eq : k = i := by omega
          subst hk_eq
          have hj1_lt : j + 1 < w.length := by omega
          rw [h_eq]
          have := hadj' j hj1_lt
          simp only [List.get_eq_getElem] at this
          convert this using 2; omega
        · omega
        · have := hadj' (k + (j - i)) (by omega)
          simp only [List.get_eq_getElem] at this
          convert this using 2 <;> omega
      obtain ⟨q, hq, hql⟩ := ih w'.length hw'_lt w' rfl hw'_len2 hw'_head hw'_last hw'_adj
      exact ⟨q, hq, by omega⟩

lemma dirDist_ge_position_on_shortest_path
    {adj : V → V → Prop} {s t : V} {p : List V}
    (hp : IsDirectedPath adj s t p)
    (hshortest : (↑(p.length - 1) : ℕ∞) = dirDist adj s t)
    (j : ℕ) (hj : 1 ≤ j) (hj2 : j < p.length) (hst : s ≠ t) :
    (↑j : ℕ∞) ≤ dirDist adj s (p.get ⟨j, hj2⟩) := by
  by_contra h_neg
  push_neg at h_neg

  rw [dirDist, sInf_lt_iff] at h_neg
  obtain ⟨b, hb_mem, hb_lt⟩ := h_neg
  obtain ⟨m, q, hq_path, hq_len, hb_eq⟩ := hb_mem
  subst hb_eq
  have hm_lt_j : m < j := ENat.coe_lt_coe.mp hb_lt
  by_cases hj_last : j + 1 < p.length
  ·
    set w := q ++ p.drop (j + 1)
    have hw_len : w.length = (m + 1) + (p.length - (j + 1)) := by
      simp [w, List.length_append, List.length_drop, hq_len]
    have hw_ge2 : w.length ≥ 2 := by omega
    have hw_head : w.head? = some s := by
      simp [w, List.head?_append, hq_path.2.1, Option.some_or]
    have hw_last : w.getLast? = some t := by
      simp only [w, List.getLast?_append, List.getLast?_drop,
        show ¬ (p.length ≤ j + 1) from by omega, ite_false, hp.2.2.1, Option.some_or]
    have hw_adj : ∀ i : ℕ, (hi : i + 1 < w.length) →
        adj (w.get ⟨i, by omega⟩) (w.get ⟨i + 1, hi⟩) := by
      intro i hi
      simp only [List.get_eq_getElem, w]
      by_cases h1 : i + 1 < q.length
      · rw [List.getElem_append_left (by omega : i < q.length),
             List.getElem_append_left h1]
        have := hq_path.2.2.2.2 i (by omega)
        simpa [List.get_eq_getElem] using this
      · push_neg at h1
        by_cases h2 : i + 1 = q.length
        · rw [List.getElem_append_left (by omega : i < q.length),
               List.getElem_append_right (by omega : q.length ≤ i + 1)]
          simp only [List.getElem_drop]
          have hq_last_elem : q[i]'(by omega) = p[j]'hj2 := by
            have hlast := hq_path.2.2.1
            rw [List.getLast?_eq_getElem?] at hlast
            have h := (List.getElem?_eq_some_iff.mp hlast).2
            have : q.length - 1 = i := by omega
            exact this ▸ h
          rw [hq_last_elem]
          have := hp.2.2.2.2 j hj_last
          simp only [List.get_eq_getElem] at this
          convert this using 2; omega
        · rw [List.getElem_append_right (by omega : q.length ≤ i),
               List.getElem_append_right (by omega : q.length ≤ i + 1)]
          simp only [List.getElem_drop]
          have h_idx_lt : j + 1 + (i - q.length) + 1 < p.length := by
            simp at hi; omega
          have := hp.2.2.2.2 (j + 1 + (i - q.length)) h_idx_lt
          simp only [List.get_eq_getElem] at this
          convert this using 2; omega
    obtain ⟨r, hr_path, hr_len⟩ := walk_to_simple_path w hw_ge2 hw_head hw_last hw_adj hst
    have hw_lt_p : w.length < p.length := by omega
    have h1 : dirDist adj s t ≤ ↑(r.length - 1) := dirDist_le_of_path hr_path
    have h2 : r.length - 1 < p.length - 1 := by have := hr_path.1; omega
    have h3 : (↑(p.length - 1) : ℕ∞) ≤ ↑(r.length - 1) := hshortest ▸ h1
    have h4 : p.length - 1 ≤ r.length - 1 := ENat.coe_le_coe.mp h3
    omega
  ·
    push_neg at hj_last
    have hj_eq : j = p.length - 1 := by omega
    have hpj_eq_t : p.get ⟨j, hj2⟩ = t := by
      have hlast := hp.2.2.1
      rw [List.getLast?_eq_getElem?] at hlast
      have h := (List.getElem?_eq_some_iff.mp hlast).2
      simp only [List.get_eq_getElem]
      convert h using 2
    rw [hpj_eq_t] at hq_path

    have h_dist_le : dirDist adj s t ≤ ↑m := by
      have := dirDist_le_of_path hq_path
      have hql : q.length - 1 = m := by omega
      rw [hql] at this; exact this
    have hshortest' : (↑(p.length - 1) : ℕ∞) ≤ ↑m := hshortest ▸ h_dist_le
    have : p.length - 1 ≤ m := ENat.coe_le_coe.mp hshortest'
    omega

lemma per_vertex_dist_bound
    (N : FlowNetwork V) (fl fl' : STFlow N)
    (p : List V) (hp_aug : IsAugmentingPath N fl p)
    (hp_shortest : (↑(p.length - 1) : ℕ∞) = residualDist N fl)
    (hflow_change : ∀ u v, ¬ EdgeOnPath p u v → ¬ EdgeOnPath p v u → fl'.f u v = fl.f u v)
    (p' : List V) (hp' : IsDirectedPath (resAdj N fl') N.s N.t p')
    (j : ℕ) (hj : 1 ≤ j) (hj2 : j < p'.length) :
    dirDist (resAdj N fl) N.s (p'.get ⟨j, hj2⟩) ≤ ↑j := by

  suffices h_gen : ∀ (k : ℕ), 1 ≤ k → (hk2 : k < p'.length) →
      dirDist (resAdj N fl) N.s (p'.get ⟨k, hk2⟩) ≤ ↑k from
    h_gen j hj hj2
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk hk2

    have hadj_new : resAdj N fl' (p'.get ⟨k - 1, by omega⟩) (p'.get ⟨k, hk2⟩) := by
      have := hp'.2.2.2.2 (k - 1) (by omega : k - 1 + 1 < p'.length)
      convert this using 2 <;> congr 1 <;> omega

    set u := p'.get ⟨k - 1, by omega⟩ with hu_def
    set v := p'.get ⟨k, hk2⟩ with hv_def

    have hp'_head : p'.get ⟨0, by omega⟩ = N.s := by
      have hhead := hp'.2.1
      rw [List.head?_eq_getElem?] at hhead
      have := (List.getElem?_eq_some_iff.mp hhead).2
      simp [List.get_eq_getElem]; exact this
    have hv_ne_s : v ≠ N.s := by
      intro heq
      have hnodup := hp'.2.2.2.1
      have h_k_eq_0 : (⟨k, hk2⟩ : Fin p'.length) = ⟨0, by omega⟩ := by
        apply hnodup.get_inj_iff.mp
        show p'.get ⟨k, hk2⟩ = p'.get ⟨0, by omega⟩
        rw [show p'.get ⟨k, hk2⟩ = v from rfl, heq, ← hp'_head]
      exact absurd (Fin.ext_iff.mp h_k_eq_0) (by omega : k ≠ 0)

    by_cases h_old : resAdj N fl u v
    ·
      by_cases hk_one : k = 1
      ·
        subst hk_one
        have hu_eq_s : u = N.s := by
          simp [hu_def, List.get_eq_getElem]; exact hp'_head
        rw [hu_eq_s] at h_old
        have h_path : IsDirectedPath (resAdj N fl) N.s v [N.s, v] := by
          refine ⟨by simp, by simp, by simp, ?_, ?_⟩
          · simp [List.nodup_cons, hv_ne_s.symm]
          · intro i hi
            simp at hi
            have hi_eq : i = 0 := by omega
            subst hi_eq; simpa [List.get_eq_getElem] using h_old
        have h1 := dirDist_le_of_path h_path
        simp at h1; exact h1
      ·
        have hk_ge2 : k ≥ 2 := by omega
        have ih_u : dirDist (resAdj N fl) N.s u ≤ ↑(k - 1) :=
          ih (k - 1) (by omega) (by omega) (by omega)

        have h_nonempty : (dirPathLengths (resAdj N fl) N.s u).Nonempty := by
          by_contra hempty
          rw [Set.not_nonempty_iff_eq_empty] at hempty
          simp [dirDist, hempty] at ih_u
        have h_inf_mem := csInf_mem h_nonempty
        obtain ⟨m, q, hq_path, hq_len, hq_eq⟩ := h_inf_mem
        have hm_le : m ≤ k - 1 := by
          have h_eq : dirDist (resAdj N fl) N.s u = ↑m := by
            unfold dirDist; exact hq_eq
          have : (↑m : ℕ∞) ≤ ↑(k - 1) := h_eq ▸ ih_u
          exact ENat.coe_le_coe.mp this


        set w := q ++ [v]
        have hw_len : w.length = m + 2 := by simp [w, hq_len]
        have hw_ge2 : w.length ≥ 2 := by omega
        have hw_head : w.head? = some N.s := by
          simp [w, List.head?_append, hq_path.2.1]
        have hw_last : w.getLast? = some v := by
          simp [w, List.getLast?_append]
        have hw_adj : ∀ i : ℕ, (hi : i + 1 < w.length) →
            resAdj N fl (w.get ⟨i, by omega⟩) (w.get ⟨i + 1, hi⟩) := by
          intro i hi
          simp only [List.get_eq_getElem, w]
          by_cases h_in_q : i + 1 < q.length
          · rw [List.getElem_append_left (by omega : i < q.length),
                 List.getElem_append_left h_in_q]
            have := hq_path.2.2.2.2 i (by omega)
            simpa [List.get_eq_getElem] using this
          · push_neg at h_in_q
            have hi_eq : i = q.length - 1 := by
              simp [w, hq_len] at hi; omega
            rw [List.getElem_append_left (by omega : i < q.length),
                List.getElem_append_right (by omega : q.length ≤ i + 1)]
            simp only [List.getElem_singleton]


            have hq_last : q[i]'(by omega) = u := by
              have hlast := hq_path.2.2.1
              rw [List.getLast?_eq_getElem?] at hlast
              have h := (List.getElem?_eq_some_iff.mp hlast).2
              have hqi : q.length - 1 = i := by omega
              exact hqi ▸ h
            rw [hq_last]
            exact h_old

        obtain ⟨r, hr_path, hr_len⟩ := walk_to_simple_path w hw_ge2 hw_head hw_last hw_adj hv_ne_s.symm

        have h_dist := dirDist_le_of_path hr_path
        have h_rlen : r.length - 1 ≤ k := by
          have := hr_path.1; omega
        calc dirDist (resAdj N fl) N.s v
            ≤ ↑(r.length - 1) := h_dist
          _ ≤ ↑k := ENat.coe_le_coe.mpr h_rlen
    ·

      have h_edge_on_p : EdgeOnPath p v u :=
        new_edge_on_reverse_path N fl fl' p hp_aug hflow_change hadj_new h_old

      obtain ⟨i, hi_v, hi_u⟩ := h_edge_on_p
      have hi_bound : i + 1 < p.length := (List.getElem?_eq_some_iff.mp hi_u).1
      have hi_lt : i < p.length := by omega
      have hpv : p.get ⟨i, hi_lt⟩ = v := by
        have := (List.getElem?_eq_some_iff.mp hi_v).2
        simp [List.get_eq_getElem]; exact this
      have hpu : p.get ⟨i + 1, hi_bound⟩ = u := by
        have := (List.getElem?_eq_some_iff.mp hi_u).2
        simp [List.get_eq_getElem]; exact this


      have hi_ge1 : 1 ≤ i := by
        by_contra h_i_lt
        push_neg at h_i_lt
        have hi_eq : i = 0 := by omega
        subst hi_eq

        have hp_head : p.get ⟨0, by omega⟩ = N.s := by
          have hhead := hp_aug.2.1
          rw [List.head?_eq_getElem?] at hhead
          have := (List.getElem?_eq_some_iff.mp hhead).2
          simp [List.get_eq_getElem]; exact this
        rw [hp_head] at hpv
        exact hv_ne_s hpv.symm
      have h_take_path := isDirectedPath_take hp_aug i hi_ge1 (by omega : i + 1 ≤ p.length)

      rw [hpv] at h_take_path

      have h_dist_v := dirDist_le_of_path h_take_path

      have h_take_len : (p.take (i + 1)).length - 1 = i := by
        simp [List.length_take]; omega
      rw [h_take_len] at h_dist_v


      have hp_shortest' : (↑(p.length - 1) : ℕ∞) = dirDist (resAdj N fl) N.s N.t := hp_shortest
      have hi1_ge1 : 1 ≤ i + 1 := by omega
      have h_ge := dirDist_ge_position_on_shortest_path hp_aug hp_shortest' (i + 1)
        hi1_ge1 hi_bound N.s_ne_t

      rw [hpu] at h_ge


      have ih_u : dirDist (resAdj N fl) N.s u ≤ ↑(k - 1) := by
        by_cases hk_one : k = 1
        · subst hk_one


          exfalso
          have hp_head : p.get ⟨0, by omega⟩ = N.s := by
            have hhead := hp_aug.2.1
            rw [List.head?_eq_getElem?] at hhead
            have := (List.getElem?_eq_some_iff.mp hhead).2
            simp [List.get_eq_getElem]; exact this
          have hu_eq : u = N.s := by
            simp [hu_def, List.get_eq_getElem]; exact hp'_head
          rw [hu_eq] at hpu
          have h_nodup_p := hp_aug.2.2.2.1
          simp [List.get_eq_getElem] at hp_head hpu
          exact absurd (h_nodup_p.getElem_inj_iff.mp (hpu.trans hp_head.symm)) (by omega)
        · exact ih (k - 1) (by omega) (by omega) (by omega)

      have h_i_le_k : i ≤ k := by
        have h1 : (↑(i + 1) : ℕ∞) ≤ ↑(k - 1) := le_trans h_ge ih_u
        have h2 : i + 1 ≤ k - 1 := ENat.coe_le_coe.mp h1
        omega
      calc dirDist (resAdj N fl) N.s v
          ≤ ↑i := h_dist_v
        _ ≤ ↑k := ENat.coe_le_coe.mpr h_i_le_k

theorem new_path_length_ge_old_dist
    (N : FlowNetwork V) (fl fl' : STFlow N)
    (h : IsShortestPathAugmentation N fl fl')
    (k : ℕ) (p' : List V)
    (hp' : IsDirectedPath (resAdj N fl') N.s N.t p')
    (hlen : p'.length = k + 1) :
    residualDist N fl ≤ ↑k := by

  obtain ⟨p, ⟨hp_aug, hp_dist⟩, _, hflow_change, _⟩ := h


  have hk_pos : 1 ≤ k := by
    have := hp'.1; omega
  have hk_lt : k < p'.length := by omega
  have h_bound := per_vertex_dist_bound N fl fl' p hp_aug hp_dist hflow_change
    p' hp' k hk_pos hk_lt

  have h_last : p'.get ⟨k, hk_lt⟩ = N.t := by
    have hlast := hp'.2.2.1
    rw [List.getLast?_eq_getElem?] at hlast
    have := (List.getElem?_eq_some_iff.mp hlast).2
    simp [List.get_eq_getElem] at this ⊢
    convert this using 2
    omega

  rw [h_last] at h_bound

  exact h_bound

theorem shortest_augmenting_path_monotone
    (N : FlowNetwork V) (fl fl' : STFlow N)
    (h : IsShortestPathAugmentation N fl fl') :
    residualDist N fl ≤ residualDist N fl' := by
  unfold residualDist dirDist
  apply le_sInf
  intro b hb
  obtain ⟨k, p', hp', hlen, hbeq⟩ := hb
  subst hbeq
  exact new_path_length_ge_old_dist N fl fl' h k p' hp' hlen

end NetworkFlow
