/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Flow.ShortestAugPath

open Finset BigOperators Classical

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsBottleneckEdge (N : FlowNetwork V) (fl : STFlow N) (p : List V)
    (hp : IsShortestAugmentingPath N fl p) (u v : V) : Prop :=
  EdgeOnPath p u v ∧
  resCap N fl u v = pathBottleneck N fl p hp.1.1

structure ShortestAugSeq (N : FlowNetwork V) (k : ℕ) where
  fl : Fin (k + 1) → STFlow N
  augments : ∀ i : Fin k, IsShortestPathAugmentation N (fl i.castSucc) (fl i.succ)

noncomputable def bottleneckCount (N : FlowNetwork V) {k : ℕ}
    (seq : ShortestAugSeq N k) (u v : V) : ℕ :=
  Finset.card (Finset.filter (fun i : Fin k =>
    ∃ (p : List V) (hp : IsShortestAugmentingPath N (seq.fl i.castSucc) p),
      IsBottleneckEdge N (seq.fl i.castSucc) p hp u v)
    Finset.univ)

lemma card_le_of_step_bound {k n : ℕ} (B : Finset (Fin k))
    (f : Fin k → ℕ)
    (hf_ge_one : ∀ i ∈ B, 1 ≤ f i)
    (hf_bound : ∀ i ∈ B, f i ≤ n - 1)
    (hf_step : ∀ i j, i ∈ B → j ∈ B → i < j → f i + 2 ≤ f j) :
    B.card ≤ n / 2 := by
  by_contra h
  push_neg at h
  set m := B.card
  have hm_pos : 0 < m := by omega
  have hcard_eq : B.card = m := rfl
  let enum := B.orderIsoOfFin hcard_eq
  have hstep : ∀ (a b : Fin m), a < b → f (enum a) + 2 ≤ f (enum b) := by
    intro a b hab
    exact hf_step _ _ (enum a).2 (enum b).2 (enum.strictMono hab)
  have hgrow : ∀ j : ℕ, (hj : j < m) →
      f (enum ⟨0, hm_pos⟩) + 2 * j ≤ f (enum ⟨j, hj⟩) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j' ih =>
      have hj' : j' < m := by omega
      have step := hstep ⟨j', hj'⟩ ⟨j' + 1, hj⟩ (Fin.mk_lt_mk.mpr (by omega))
      have prev := ih hj'
      omega
  have key := hgrow (m - 1) (by omega)
  have hbound := hf_bound (enum ⟨m - 1, by omega⟩) (enum ⟨m - 1, by omega⟩).2
  have hge := hf_ge_one (enum ⟨0, hm_pos⟩) (enum ⟨0, hm_pos⟩).2
  omega

theorem dirDist_lt_top_le
    (adj : V → V → Prop) (s v : V)
    (hfin : dirDist adj s v ≠ ⊤) :
    dirDist adj s v ≤ ↑(Fintype.card V - 1) := by
  have hne : (dirPathLengths adj s v).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have : dirDist adj s v = ⊤ := by
      unfold dirDist
      rw [hempty]
      exact sInf_empty
    exact hfin this
  have hbound : ∀ x ∈ dirPathLengths adj s v, x ≤ ↑(Fintype.card V - 1) := by
    intro x hx
    obtain ⟨k, p, hp, hlen, hxeq⟩ := hx
    subst hxeq
    apply WithTop.coe_le_coe.mpr
    have hnodup := hp.2.2.2.1
    have hcard := hnodup.length_le_card
    omega
  unfold dirDist
  obtain ⟨x, hx⟩ := hne
  exact le_trans (csInf_le (OrderBot.bddBelow _) hx) (hbound x hx)

lemma per_vertex_dist_bound_general
    (N : FlowNetwork V) (fl fl' : STFlow N)
    (p : List V) (hp_aug : IsAugmentingPath N fl p)
    (hp_shortest : (↑(p.length - 1) : ℕ∞) = residualDist N fl)
    (hflow_change : ∀ u v, ¬ EdgeOnPath p u v → ¬ EdgeOnPath p v u → fl'.f u v = fl.f u v)
    (v : V) (p' : List V) (hp' : IsDirectedPath (resAdj N fl') N.s v p')
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
    set w := p'.get ⟨k, hk2⟩ with hw_def

    have hp'_head : p'.get ⟨0, by omega⟩ = N.s := by
      have hhead := hp'.2.1
      rw [List.head?_eq_getElem?] at hhead
      have := (List.getElem?_eq_some_iff.mp hhead).2
      simp [List.get_eq_getElem]; exact this
    have hw_ne_s : w ≠ N.s := by
      intro heq
      have hnodup := hp'.2.2.2.1
      have h_k_eq_0 : (⟨k, hk2⟩ : Fin p'.length) = ⟨0, by omega⟩ := by
        apply hnodup.get_inj_iff.mp
        show p'.get ⟨k, hk2⟩ = p'.get ⟨0, by omega⟩
        rw [show p'.get ⟨k, hk2⟩ = w from rfl, heq, ← hp'_head]
      exact absurd (Fin.ext_iff.mp h_k_eq_0) (by omega : k ≠ 0)

    by_cases h_old : resAdj N fl u w
    ·
      by_cases hk_one : k = 1
      ·
        subst hk_one
        have hu_eq_s : u = N.s := by
          simp [hu_def, List.get_eq_getElem]; exact hp'_head
        rw [hu_eq_s] at h_old
        have h_path : IsDirectedPath (resAdj N fl) N.s w [N.s, w] := by
          refine ⟨by simp, by simp, by simp, ?_, ?_⟩
          · simp [List.nodup_cons, hw_ne_s.symm]
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
        set wr := q ++ [w]
        have hwr_len : wr.length = m + 2 := by simp [wr, hq_len]
        have hwr_ge2 : wr.length ≥ 2 := by omega
        have hwr_head : wr.head? = some N.s := by
          simp [wr, List.head?_append, hq_path.2.1]
        have hwr_last : wr.getLast? = some w := by
          simp [wr, List.getLast?_append]
        have hwr_adj : ∀ i : ℕ, (hi : i + 1 < wr.length) →
            resAdj N fl (wr.get ⟨i, by omega⟩) (wr.get ⟨i + 1, hi⟩) := by
          intro i hi
          simp only [List.get_eq_getElem, wr]
          by_cases h_in_q : i + 1 < q.length
          · rw [List.getElem_append_left (by omega : i < q.length),
                 List.getElem_append_left h_in_q]
            have := hq_path.2.2.2.2 i (by omega)
            simpa [List.get_eq_getElem] using this
          · push_neg at h_in_q
            have hi_eq : i = q.length - 1 := by
              simp [wr, hq_len] at hi; omega
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
        obtain ⟨r, hr_path, hr_len⟩ := walk_to_simple_path wr hwr_ge2 hwr_head hwr_last hwr_adj hw_ne_s.symm
        have h_dist := dirDist_le_of_path hr_path
        have h_rlen : r.length - 1 ≤ k := by
          have := hr_path.1; omega
        calc dirDist (resAdj N fl) N.s w
            ≤ ↑(r.length - 1) := h_dist
          _ ≤ ↑k := ENat.coe_le_coe.mpr h_rlen
    ·
      have h_edge_on_p : EdgeOnPath p w u :=
        new_edge_on_reverse_path N fl fl' p hp_aug hflow_change hadj_new h_old
      obtain ⟨i, hi_w, hi_u⟩ := h_edge_on_p
      have hi_bound : i + 1 < p.length := (List.getElem?_eq_some_iff.mp hi_u).1
      have hi_lt : i < p.length := by omega
      have hpw : p.get ⟨i, hi_lt⟩ = w := by
        have := (List.getElem?_eq_some_iff.mp hi_w).2
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
        rw [hp_head] at hpw
        exact hw_ne_s hpw.symm
      have h_take_path := isDirectedPath_take hp_aug i hi_ge1 (by omega : i + 1 ≤ p.length)
      rw [hpw] at h_take_path
      have h_dist_w := dirDist_le_of_path h_take_path
      have h_take_len : (p.take (i + 1)).length - 1 = i := by
        simp [List.length_take]; omega
      rw [h_take_len] at h_dist_w
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
      calc dirDist (resAdj N fl) N.s w
          ≤ ↑i := h_dist_w
        _ ≤ ↑k := ENat.coe_le_coe.mpr h_i_le_k

theorem new_path_length_ge_old_dist_general
    (N : FlowNetwork V) (fl fl' : STFlow N)
    (h : IsShortestPathAugmentation N fl fl')
    (v : V) (k : ℕ) (p' : List V)
    (hp' : IsDirectedPath (resAdj N fl') N.s v p')
    (hlen : p'.length = k + 1) :
    dirDist (resAdj N fl) N.s v ≤ ↑k := by
  obtain ⟨p, ⟨hp_aug, hp_dist⟩, _, hflow_change, _⟩ := h
  have hk_pos : 1 ≤ k := by have := hp'.1; omega
  have hk_lt : k < p'.length := by omega
  have h_bound := per_vertex_dist_bound_general N fl fl' p hp_aug hp_dist hflow_change
    v p' hp' k hk_pos hk_lt

  have h_last : p'.get ⟨k, hk_lt⟩ = v := by
    have hlast := hp'.2.2.1
    rw [List.getLast?_eq_getElem?] at hlast
    have := (List.getElem?_eq_some_iff.mp hlast).2
    simp [List.get_eq_getElem] at this ⊢
    convert this using 2
    omega
  rw [h_last] at h_bound
  exact h_bound

theorem vertex_dist_monotone
    (N : FlowNetwork V) (fl fl' : STFlow N)
    (h : IsShortestPathAugmentation N fl fl') (v : V) :
    dirDist (resAdj N fl) N.s v ≤ dirDist (resAdj N fl') N.s v := by
  unfold dirDist
  apply le_sInf
  intro b hb
  obtain ⟨k, p', hp', hlen, hbeq⟩ := hb
  subst hbeq
  exact new_path_length_ge_old_dist_general N fl fl' h v k p' hp' hlen

theorem dist_on_shortest_path
    (N : FlowNetwork V) (fl : STFlow N) (p : List V)
    (hp : IsShortestAugmentingPath N fl p) (u v : V)
    (huv : EdgeOnPath p u v)
    (hfin_u : dirDist (resAdj N fl) N.s u ≠ ⊤) :
    dirDist (resAdj N fl) N.s v = dirDist (resAdj N fl) N.s u + 1 := by

  obtain ⟨i, hi_u, hi_v⟩ := huv

  have hp_aug := hp.1
  have hp_shortest := hp.2
  have hlen := hp_aug.1
  have hnodup := hp_aug.2.2.2.1

  have hi_lt : i < p.length := by
    by_contra h; push_neg at h
    rw [List.getElem?_eq_none (by omega)] at hi_u; exact absurd hi_u (by simp)
  have hi1_lt : i + 1 < p.length := by
    by_contra h; push_neg at h
    rw [List.getElem?_eq_none (by omega)] at hi_v; exact absurd hi_v (by simp)

  have hpi : p[i] = u := by
    have := List.getElem?_eq_getElem hi_lt; rw [this] at hi_u
    exact Option.some_injective _ hi_u
  have hpi1 : p[i + 1] = v := by
    have := List.getElem?_eq_getElem hi1_lt; rw [this] at hi_v
    exact Option.some_injective _ hi_v

  have hi_pos : i ≥ 1 := by
    by_contra h_lt; push_neg at h_lt
    have hi_eq : i = 0 := by omega
    subst hi_eq

    have hp0 : p[0] = N.s := by
      have hhead := hp_aug.2.1
      rw [List.head?_eq_getElem?] at hhead
      have h0_lt : (0 : ℕ) < p.length := by omega
      rw [List.getElem?_eq_getElem h0_lt] at hhead
      exact Option.some_injective _ hhead
    have hu_eq_s : u = N.s := hpi.symm.trans hp0

    have h_top : dirDist (resAdj N fl) N.s N.s = ⊤ := by
      unfold dirDist
      suffices h_empty : dirPathLengths (resAdj N fl) N.s N.s = ∅ from by
        rw [h_empty]; exact sInf_empty
      ext x; simp only [Set.mem_empty_iff_false, iff_false]
      intro ⟨k, q, hq, _, _⟩

      have hq_nodup := hq.2.2.2.1
      have hq_head := hq.2.1
      have hq_last := hq.2.2.1
      have hq_len := hq.1

      have hq0 : q[0]'(by omega) = N.s := by
        rw [List.head?_eq_getElem?] at hq_head
        have := List.getElem?_eq_getElem (by omega : 0 < q.length)
        rw [this] at hq_head; exact Option.some_injective _ hq_head
      have hqlast : q[q.length - 1]'(by omega) = N.s := by
        rw [List.getLast?_eq_getElem?] at hq_last
        have := (List.getElem?_eq_some_iff.mp hq_last).2
        exact this

      have h_same : q[0]'(by omega) = q[q.length - 1]'(by omega) :=
        hq0.trans hqlast.symm
      have h_ne_idx : (0 : ℕ) ≠ q.length - 1 := by omega
      have h_idx_eq := hq_nodup.getElem_inj_iff.mp h_same
      simp [Fin.ext_iff] at h_idx_eq
      exact absurd h_idx_eq h_ne_idx
    rw [hu_eq_s] at hfin_u
    exact absurd h_top hfin_u


  have hp_dir : IsDirectedPath (resAdj N fl) N.s N.t p := hp_aug

  have hshortest : (↑(p.length - 1) : ℕ∞) = dirDist (resAdj N fl) N.s N.t := hp_shortest

  have h_get_v : p.get ⟨i + 1, hi1_lt⟩ = v := by simp [List.get_eq_getElem]; exact hpi1
  have h_get_u : p.get ⟨i, hi_lt⟩ = u := by simp [List.get_eq_getElem]; exact hpi

  have h_take_v := isDirectedPath_take hp_dir (i + 1) (by omega) (by omega : i + 1 + 1 ≤ p.length)
  rw [h_get_v] at h_take_v
  have h_take_v_len : (p.take (i + 2)).length - 1 = i + 1 := by
    simp [List.length_take]; omega
  have h_le : dirDist (resAdj N fl) N.s v ≤ ↑(i + 1) := by
    have hle := dirDist_le_of_path h_take_v
    rw [h_take_v_len] at hle
    exact hle

  have h_ge : (↑(i + 1) : ℕ∞) ≤ dirDist (resAdj N fl) N.s v := by
    have hge := dirDist_ge_position_on_shortest_path hp_dir hshortest (i + 1) (by omega) hi1_lt N.s_ne_t
    rw [h_get_v] at hge
    exact hge

  have h_dist_v : dirDist (resAdj N fl) N.s v = ↑(i + 1) := le_antisymm h_le h_ge

  have h_take_u := isDirectedPath_take hp_dir i hi_pos (by omega : i + 1 ≤ p.length)
  rw [h_get_u] at h_take_u
  have h_take_u_len : (p.take (i + 1)).length - 1 = i := by
    simp [List.length_take]; omega
  have h_le_u : dirDist (resAdj N fl) N.s u ≤ ↑i := by
    have hle := dirDist_le_of_path h_take_u
    rw [h_take_u_len] at hle
    exact hle

  have h_ge_u : (↑i : ℕ∞) ≤ dirDist (resAdj N fl) N.s u := by
    have hge := dirDist_ge_position_on_shortest_path hp_dir hshortest i hi_pos hi_lt N.s_ne_t
    rw [h_get_u] at hge
    exact hge

  have h_dist_u : dirDist (resAdj N fl) N.s u = ↑i := le_antisymm h_le_u h_ge_u

  rw [h_dist_v, h_dist_u]
  norm_cast

theorem dist_finite_on_path
    (N : FlowNetwork V) (fl : STFlow N) (p : List V)
    (hp : IsShortestAugmentingPath N fl p) (u v : V)
    (huv : EdgeOnPath p u v) (hne : u ≠ N.s) :
    dirDist (resAdj N fl) N.s u ≠ ⊤ := by
  obtain ⟨i, hi_u, hi_v⟩ := huv
  have hp_aug := hp.1
  have hlen := hp_aug.1
  have hhead := hp_aug.2.1
  have hnodup := hp_aug.2.2.2.1
  have hadj := hp_aug.2.2.2.2

  have hi_lt : i < p.length := by
    by_contra h
    push_neg at h
    rw [List.getElem?_eq_none (by omega)] at hi_u
    exact absurd hi_u (by simp)

  have hi1_lt : i + 1 < p.length := by
    by_contra h
    push_neg at h
    rw [List.getElem?_eq_none (by omega)] at hi_v
    exact absurd hi_v (by simp)

  have hpi : p[i] = u := by
    have := List.getElem?_eq_getElem hi_lt
    rw [this] at hi_u
    exact Option.some_injective _ hi_u

  have hp0 : p[0] = N.s := by
    have h0 : (0 : ℕ) < p.length := by omega
    have := List.getElem?_eq_getElem h0
    rw [List.head?_eq_getElem?] at hhead
    rw [this] at hhead
    exact Option.some_injective _ hhead

  have hi0 : i ≠ 0 := by
    intro heq; subst heq; exact hne (hpi.symm.trans hp0)
  have hi_pos : i ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi0

  have hprefix_len : (p.take (i + 1)).length = i + 1 := by
    rw [List.length_take]
    omega
  have hprefix_ge2 : (p.take (i + 1)).length ≥ 2 := by
    rw [hprefix_len]; omega
  have hprefix_head : (p.take (i + 1)).head? = some N.s := by
    rw [List.head?_eq_getElem?, List.getElem?_take]
    simp only [show (0 : ℕ) < i + 1 from by omega, ite_true]
    rw [List.head?_eq_getElem?] at hhead
    exact hhead
  have hprefix_last : (p.take (i + 1)).getLast? = some u := by
    rw [List.getLast?_eq_getElem?, hprefix_len]
    simp only [Nat.add_sub_cancel]
    rw [List.getElem?_take]
    simp only [show i < i + 1 from by omega, ite_true]
    rw [List.getElem?_eq_getElem hi_lt, hpi]
  have hprefix_nodup : (p.take (i + 1)).Nodup :=
    hnodup.sublist (List.take_prefix (i + 1) p).sublist
  have hprefix_adj : ∀ j : ℕ, (hj : j + 1 < (p.take (i + 1)).length) →
      resAdj N fl ((p.take (i + 1)).get ⟨j, by omega⟩)
        ((p.take (i + 1)).get ⟨j + 1, hj⟩) := by
    intro j hj
    rw [hprefix_len] at hj
    simp only [List.get_eq_getElem, List.getElem_take]
    exact hadj j (by omega)

  have hmem : (↑i : ℕ∞) ∈ dirPathLengths (resAdj N fl) N.s u := by
    exact ⟨i, p.take (i + 1),
      ⟨hprefix_ge2, hprefix_head, hprefix_last, hprefix_nodup, hprefix_adj⟩,
      hprefix_len, rfl⟩

  intro h_top
  have hle : dirDist (resAdj N fl) N.s u ≤ ↑i :=
    csInf_le (OrderBot.bddBelow _) hmem
  rw [h_top] at hle
  exact absurd hle (by simp)

lemma vertex_dist_monotone_seq
    (N : FlowNetwork V) {k : ℕ}
    (seq : ShortestAugSeq N k) (w : V)
    (a b : Fin (k + 1)) (hab : a ≤ b) :
    dirDist (resAdj N (seq.fl a)) N.s w ≤ dirDist (resAdj N (seq.fl b)) N.s w := by
  obtain ⟨d, hd⟩ : ∃ d, (a : ℕ) + d = (b : ℕ) := ⟨b - a, by omega⟩
  induction d generalizing a b with
  | zero =>
    have : a = b := by ext; omega
    subst this; exact le_refl _
  | succ d ih =>
    have hb_pos : (0 : ℕ) < (b : ℕ) := by omega
    have hb_val : (b : ℕ) - 1 < k + 1 := by omega
    set b' : Fin (k + 1) := ⟨(b : ℕ) - 1, hb_val⟩
    have hab' : a ≤ b' := by exact_mod_cast (show (a : ℕ) ≤ b'.val by simp [b']; omega)
    have hd' : (a : ℕ) + d = (b' : ℕ) := by simp [b']; omega
    have step1 : dirDist (resAdj N (seq.fl a)) N.s w ≤
        dirDist (resAdj N (seq.fl b')) N.s w := ih a b' hab' hd'

    have hb'_lt_k : b'.val < k := by simp [b']; omega
    have step2 : dirDist (resAdj N (seq.fl b')) N.s w ≤
        dirDist (resAdj N (seq.fl b)) N.s w := by
      have haug := seq.augments ⟨b'.val, hb'_lt_k⟩
      have hmono := vertex_dist_monotone N _ _ haug w
      have heq1 : ((⟨b'.val, hb'_lt_k⟩ : Fin k).castSucc : Fin (k+1)) = b' := by
        ext; simp [Fin.castSucc]
      have heq2 : ((⟨b'.val, hb'_lt_k⟩ : Fin k).succ : Fin (k+1)) = b := by
        ext; simp [Fin.succ, b']; omega
      rw [heq1, heq2] at hmono
      exact hmono
    exact le_trans step1 step2

lemma source_not_interior_of_augmenting_path
    (N : FlowNetwork V) (fl : STFlow N) (p : List V)
    (hp : IsAugmentingPath N fl p) (w : V) :
    ¬ EdgeOnPath p w N.s := by
  intro ⟨idx, _, hidx_s⟩
  have hhead := hp.2.1
  have hnodup := hp.2.2.2.1
  have hidx1_lt : idx + 1 < p.length := by
    by_contra h; push_neg at h
    rw [List.getElem?_eq_none (by omega)] at hidx_s
    exact absurd hidx_s (by simp)
  have hp_idx1 : p[idx + 1] = N.s := by
    have := List.getElem?_eq_getElem hidx1_lt
    rw [this] at hidx_s
    exact Option.some_injective _ hidx_s
  have hp0 : p[0]'(by omega) = N.s := by
    rw [List.head?_eq_getElem?] at hhead
    have h0lt : (0 : ℕ) < p.length := by omega
    have := List.getElem?_eq_getElem h0lt
    rw [this] at hhead
    exact Option.some_injective _ hhead
  have hne_idx : idx + 1 ≠ 0 := by omega
  have heq : p[idx + 1] = p[0]'(by omega) := hp_idx1.trans hp0.symm
  exact hne_idx (hnodup.getElem_inj_iff.mp heq)

lemma bottleneck_saturated_after_augmentation
    (N : FlowNetwork V) (fl fl' : STFlow N) (p : List V)
    (hp : IsShortestAugmentingPath N fl p) (u v : V)
    (hbot : IsBottleneckEdge N fl p hp u v)
    (haug : IsShortestPathAugmentation N fl fl') :
    ¬ resAdj N fl' u v := by
  obtain ⟨_, _, _, _, hsat⟩ := haug
  exact hsat p hp u v hbot.1 hbot.2

theorem source_edge_bottleneck_at_most_once
    (N : FlowNetwork V) {k : ℕ}
    (seq : ShortestAugSeq N k) (v : V)
    (i j : Fin k) (hij : i < j)
    (p_i : List V) (hp_i : IsShortestAugmentingPath N (seq.fl i.castSucc) p_i)
    (hbot_i : IsBottleneckEdge N (seq.fl i.castSucc) p_i hp_i N.s v)
    (p_j : List V) (hp_j : IsShortestAugmentingPath N (seq.fl j.castSucc) p_j)
    (hbot_j : IsBottleneckEdge N (seq.fl j.castSucc) p_j hp_j N.s v) :
    False := by

  have haug_i := seq.augments i
  have hsat_after_i : ¬ resAdj N (seq.fl i.succ) N.s v :=
    bottleneck_saturated_after_augmentation N (seq.fl i.castSucc) (seq.fl i.succ)
      p_i hp_i N.s v hbot_i haug_i

  have h_persist : ∀ (m : Fin (k + 1)), (i.succ : Fin (k + 1)) ≤ m →
      m ≤ (j.castSucc : Fin (k + 1)) → ¬ resAdj N (seq.fl m) N.s v := by
    intro m hm_lo hm_hi
    have hm_lo_nat : (i : ℕ) + 1 ≤ (m : ℕ) := by
      exact_mod_cast hm_lo
    have hm_hi_nat : (m : ℕ) ≤ (j : ℕ) := by
      exact_mod_cast hm_hi

    suffices h : ∀ (gap : ℕ) (m : Fin (k + 1)),
        (i : ℕ) + 1 ≤ (m : ℕ) → (m : ℕ) ≤ (j : ℕ) →
        gap = (m : ℕ) - ((i : ℕ) + 1) →
        ¬ resAdj N (seq.fl m) N.s v from h _ m hm_lo_nat hm_hi_nat rfl

    intro gap
    induction gap with
    | zero =>
      intro m hlo hhi hgap
      have hm_eq : (m : ℕ) = (i : ℕ) + 1 := by omega
      have hm_eq_fin : m = i.succ := by ext; simp [Fin.succ]; exact hm_eq
      rw [hm_eq_fin]; exact hsat_after_i
    | succ gap' ih =>
      intro m hlo hhi hgap

      have hm_gt : (i : ℕ) + 1 < (m : ℕ) := by omega
      have hm_pred_bound : (m : ℕ) - 1 < k + 1 := by omega
      set m' : Fin (k + 1) := ⟨(m : ℕ) - 1, hm_pred_bound⟩
      have hm'_lo : (i : ℕ) + 1 ≤ (m' : ℕ) := by simp [m']; omega
      have hm'_hi : (m' : ℕ) ≤ (j : ℕ) := by simp [m']; omega
      have hm'_gap : gap' = (m' : ℕ) - ((i : ℕ) + 1) := by simp [m']; omega

      have h_not_at_m' : ¬ resAdj N (seq.fl m') N.s v := ih m' hm'_lo hm'_hi hm'_gap

      have hm'_lt_k : m'.val < k := by simp [m']; omega
      have haug_m' := seq.augments ⟨m'.val, hm'_lt_k⟩
      have hm_eq_succ : (⟨m'.val, hm'_lt_k⟩ : Fin k).succ = m := by
        ext; simp [Fin.succ, m']; omega
      have hm'_cast : (⟨m'.val, hm'_lt_k⟩ : Fin k).castSucc = m' := by
        ext; simp [Fin.castSucc]
      rw [hm'_cast, hm_eq_succ] at haug_m'
      obtain ⟨p_m', hp_m'_short, _, hflow_change_m', _⟩ := haug_m'
      have h_not_on_m' : ¬ EdgeOnPath p_m' N.s v := by
        intro ⟨idx, h_idx_s, h_idx_v⟩
        have hp_m'_aug := hp_m'_short.1
        have hadj_m' := hp_m'_aug.2.2.2.2
        have h_idx_lt : idx < p_m'.length := by
          by_contra h; push_neg at h
          rw [List.getElem?_eq_none (by omega)] at h_idx_s
          exact absurd h_idx_s (by simp)
        have h_idx1_lt : idx + 1 < p_m'.length := by
          by_contra h; push_neg at h
          rw [List.getElem?_eq_none (by omega)] at h_idx_v
          exact absurd h_idx_v (by simp)
        have h_s_eq : p_m'.get ⟨idx, by omega⟩ = N.s := by
          have := List.getElem?_eq_getElem h_idx_lt
          rw [this] at h_idx_s
          simp [List.get_eq_getElem]
          exact Option.some_injective _ h_idx_s
        have h_v_eq : p_m'.get ⟨idx + 1, h_idx1_lt⟩ = v := by
          have := List.getElem?_eq_getElem h_idx1_lt
          rw [this] at h_idx_v
          simp [List.get_eq_getElem]
          exact Option.some_injective _ h_idx_v
        have := hadj_m' idx h_idx1_lt
        rw [h_s_eq, h_v_eq] at this
        exact h_not_at_m' this
      have h_not_rev_m' : ¬ EdgeOnPath p_m' v N.s :=
        source_not_interior_of_augmenting_path N (seq.fl m') p_m' hp_m'_short.1 v
      have hf_sv : (seq.fl m).f N.s v = (seq.fl m').f N.s v :=
        hflow_change_m' N.s v h_not_on_m' h_not_rev_m'
      have hf_vs : (seq.fl m).f v N.s = (seq.fl m').f v N.s := by
        have h1 : ¬ EdgeOnPath p_m' v N.s :=
          source_not_interior_of_augmenting_path N (seq.fl m') p_m' hp_m'_short.1 v
        have h2 : ¬ EdgeOnPath p_m' N.s v := h_not_on_m'
        exact hflow_change_m' v N.s h1 h2
      show ¬ resAdj N (seq.fl m) N.s v
      unfold resAdj resCap
      rw [hf_sv, hf_vs]
      unfold resAdj resCap at h_not_at_m'
      linarith


  have h_not_at_j : ¬ resAdj N (seq.fl j.castSucc) N.s v :=
    h_persist j.castSucc (by show (i.succ : ℕ) ≤ (j.castSucc : ℕ); simp [Fin.succ, Fin.castSucc]; omega) le_rfl


  have h_on_j : EdgeOnPath p_j N.s v := hbot_j.1
  obtain ⟨idx_j, h_idx_j_s, h_idx_j_v⟩ := h_on_j
  have hp_j_aug := hp_j.1
  have hadj_j := hp_j_aug.2.2.2.2
  have h_idx_j_lt : idx_j < p_j.length := by
    by_contra h; push_neg at h
    rw [List.getElem?_eq_none (by omega)] at h_idx_j_s
    exact absurd h_idx_j_s (by simp)
  have h_idx_j1_lt : idx_j + 1 < p_j.length := by
    by_contra h; push_neg at h
    rw [List.getElem?_eq_none (by omega)] at h_idx_j_v
    exact absurd h_idx_j_v (by simp)
  have h_s_eq_j : p_j.get ⟨idx_j, by omega⟩ = N.s := by
    have := List.getElem?_eq_getElem h_idx_j_lt
    rw [this] at h_idx_j_s
    simp [List.get_eq_getElem]; exact Option.some_injective _ h_idx_j_s
  have h_v_eq_j : p_j.get ⟨idx_j + 1, h_idx_j1_lt⟩ = v := by
    have := List.getElem?_eq_getElem h_idx_j1_lt
    rw [this] at h_idx_j_v
    simp [List.get_eq_getElem]; exact Option.some_injective _ h_idx_j_v
  have h_resAdj_j : resAdj N (seq.fl j.castSucc) N.s v := by
    have := hadj_j idx_j h_idx_j1_lt
    rw [h_s_eq_j, h_v_eq_j] at this
    exact this
  exact h_not_at_j h_resAdj_j

theorem dist_increase_between_bottlenecks
    (N : FlowNetwork V) {k : ℕ}
    (seq : ShortestAugSeq N k) (u v : V)
    (i j : Fin k) (hij : i < j)
    (p_i : List V) (hp_i : IsShortestAugmentingPath N (seq.fl i.castSucc) p_i)
    (hbot_i : IsBottleneckEdge N (seq.fl i.castSucc) p_i hp_i u v)
    (p_j : List V) (hp_j : IsShortestAugmentingPath N (seq.fl j.castSucc) p_j)
    (hbot_j : IsBottleneckEdge N (seq.fl j.castSucc) p_j hp_j u v) :
    dirDist (resAdj N (seq.fl i.castSucc)) N.s u + 2 ≤
    dirDist (resAdj N (seq.fl j.castSucc)) N.s u := by


  have hu_ne_s : u ≠ N.s := by
    intro heq
    subst heq
    exact source_edge_bottleneck_at_most_once N seq v i j hij p_i hp_i hbot_i p_j hp_j hbot_j
  have hfin_i : dirDist (resAdj N (seq.fl i.castSucc)) N.s u ≠ ⊤ :=
    dist_finite_on_path N (seq.fl i.castSucc) p_i hp_i u v hbot_i.1 hu_ne_s
  have hdist_i_v : dirDist (resAdj N (seq.fl i.castSucc)) N.s v =
      dirDist (resAdj N (seq.fl i.castSucc)) N.s u + 1 :=
    dist_on_shortest_path N (seq.fl i.castSucc) p_i hp_i u v hbot_i.1 hfin_i


  have ⟨m, hm_range, hm_aug, hm_edge⟩ : ∃ (m : Fin k),
      (i < m ∧ m ≤ j) ∧
      IsShortestPathAugmentation N (seq.fl m.castSucc) (seq.fl m.succ) ∧
      (∃ (p_m : List V) (hp_m : IsShortestAugmentingPath N (seq.fl m.castSucc) p_m),
        EdgeOnPath p_m v u) := by


    by_contra h_no_m


    have h_resAdj_j : resAdj N (seq.fl j.castSucc) u v := by
      obtain ⟨idx_j, h_idx_j_u, h_idx_j_v⟩ := hbot_j.1
      have hp_j_aug := hp_j.1
      have hadj_j := hp_j_aug.2.2.2.2
      have h_idx_j_lt : idx_j < p_j.length := by
        by_contra h; push_neg at h
        rw [List.getElem?_eq_none (by omega)] at h_idx_j_u
        exact absurd h_idx_j_u (by simp)
      have h_idx_j1_lt : idx_j + 1 < p_j.length := by
        by_contra h; push_neg at h
        rw [List.getElem?_eq_none (by omega)] at h_idx_j_v
        exact absurd h_idx_j_v (by simp)
      have h_u_eq : p_j.get ⟨idx_j, by omega⟩ = u := by
        have := List.getElem?_eq_getElem h_idx_j_lt
        rw [this] at h_idx_j_u
        simp [List.get_eq_getElem]
        exact Option.some_injective _ h_idx_j_u
      have h_v_eq : p_j.get ⟨idx_j + 1, h_idx_j1_lt⟩ = v := by
        have := List.getElem?_eq_getElem h_idx_j1_lt
        rw [this] at h_idx_j_v
        simp [List.get_eq_getElem]
        exact Option.some_injective _ h_idx_j_v
      have := hadj_j idx_j h_idx_j1_lt
      rw [h_u_eq, h_v_eq] at this
      exact this

    have hsat : ¬ resAdj N (seq.fl i.succ) u v :=
      bottleneck_saturated_after_augmentation N (seq.fl i.castSucc) (seq.fl i.succ)
        p_i hp_i u v hbot_i (seq.augments i)

    suffices h_persist : ∀ (gap : ℕ) (m_fin : Fin (k + 1)),
        (i : ℕ) + 1 ≤ (m_fin : ℕ) → (m_fin : ℕ) ≤ (j : ℕ) →
        gap = (m_fin : ℕ) - ((i : ℕ) + 1) →
        ¬ resAdj N (seq.fl m_fin) u v by
      have h_at_j := h_persist ((j : ℕ) - ((i : ℕ) + 1)) j.castSucc
        (by simp [Fin.castSucc]; omega) (by simp [Fin.castSucc]) rfl
      exact h_at_j h_resAdj_j
    intro gap
    induction gap with
    | zero =>
      intro m_fin hlo _hhi hgap
      have hm_eq : (m_fin : ℕ) = (i : ℕ) + 1 := by omega
      have hm_eq_fin : m_fin = i.succ := by ext; simp [Fin.succ]; exact hm_eq
      rw [hm_eq_fin]; exact hsat
    | succ gap' ih =>
      intro m_fin hlo hhi hgap
      have hm_gt : (i : ℕ) + 1 < (m_fin : ℕ) := by omega
      have hm_pred_bound : (m_fin : ℕ) - 1 < k + 1 := by omega
      set m' : Fin (k + 1) := ⟨(m_fin : ℕ) - 1, hm_pred_bound⟩
      have hm'_lo : (i : ℕ) + 1 ≤ (m' : ℕ) := by simp [m']; omega
      have hm'_hi : (m' : ℕ) ≤ (j : ℕ) := by simp [m']; omega
      have hm'_gap : gap' = (m' : ℕ) - ((i : ℕ) + 1) := by simp [m']; omega
      have h_not_at_m' : ¬ resAdj N (seq.fl m') u v := ih m' hm'_lo hm'_hi hm'_gap

      have hm'_lt_k : m'.val < k := by simp [m']; omega
      have haug_m' := seq.augments ⟨m'.val, hm'_lt_k⟩
      have hm_eq_succ : (⟨m'.val, hm'_lt_k⟩ : Fin k).succ = m_fin := by
        ext; simp [Fin.succ, m']; omega
      have hm'_cast : (⟨m'.val, hm'_lt_k⟩ : Fin k).castSucc = m' := by
        ext; simp [Fin.castSucc]
      rw [hm'_cast, hm_eq_succ] at haug_m'
      obtain ⟨p_m', hp_m'_short, _, hflow_change_m', _⟩ := haug_m'


      have h_not_uv_m' : ¬ EdgeOnPath p_m' u v := by
        intro ⟨idx, h_idx_u, h_idx_v⟩
        have hp_m'_aug := hp_m'_short.1
        have hadj_m' := hp_m'_aug.2.2.2.2
        have h_idx_lt : idx < p_m'.length := by
          by_contra h; push_neg at h
          rw [List.getElem?_eq_none (by omega)] at h_idx_u
          exact absurd h_idx_u (by simp)
        have h_idx1_lt : idx + 1 < p_m'.length := by
          by_contra h; push_neg at h
          rw [List.getElem?_eq_none (by omega)] at h_idx_v
          exact absurd h_idx_v (by simp)
        have h_u_eq : p_m'.get ⟨idx, by omega⟩ = u := by
          have := List.getElem?_eq_getElem h_idx_lt
          rw [this] at h_idx_u
          simp [List.get_eq_getElem]
          exact Option.some_injective _ h_idx_u
        have h_v_eq : p_m'.get ⟨idx + 1, h_idx1_lt⟩ = v := by
          have := List.getElem?_eq_getElem h_idx1_lt
          rw [this] at h_idx_v
          simp [List.get_eq_getElem]
          exact Option.some_injective _ h_idx_v
        have := hadj_m' idx h_idx1_lt
        rw [h_u_eq, h_v_eq] at this
        exact h_not_at_m' this

      have h_not_vu_m' : ¬ EdgeOnPath p_m' v u := by
        intro hvu_on
        apply h_no_m
        refine ⟨⟨m'.val, hm'_lt_k⟩, ⟨?_, ?_⟩, seq.augments ⟨m'.val, hm'_lt_k⟩,
          p_m', ?_, hvu_on⟩
        ·
          exact Fin.val_fin_lt.mp (by simp [m']; omega)
        ·
          exact Fin.val_fin_le.mp (by simp [m']; omega)
        ·
          have : (⟨m'.val, hm'_lt_k⟩ : Fin k).castSucc = m' := hm'_cast
          rw [this]
          exact hp_m'_short

      have hf_uv : (seq.fl m_fin).f u v = (seq.fl m').f u v :=
        hflow_change_m' u v h_not_uv_m' h_not_vu_m'
      have hf_vu : (seq.fl m_fin).f v u = (seq.fl m').f v u := by
        have h1 : ¬ EdgeOnPath p_m' v u := h_not_vu_m'
        have h2 : ¬ EdgeOnPath p_m' u v := h_not_uv_m'
        exact hflow_change_m' v u h1 h2
      show ¬ resAdj N (seq.fl m_fin) u v
      unfold resAdj resCap
      rw [hf_uv, hf_vu]
      unfold resAdj resCap at h_not_at_m'
      linarith
  obtain ⟨him, hmj⟩ := hm_range
  obtain ⟨p_m, hp_m, hvu_on_m⟩ := hm_edge


  have hv_ne_s : v ≠ N.s := by
    obtain ⟨i_pos, hi_pos_u, hi_pos_v⟩ := hbot_i.1
    have hp_aug_i := hp_i.1
    have hnodup_i := hp_aug_i.2.2.2.1
    have hhead_i := hp_aug_i.2.1
    have hlen_i := hp_aug_i.1
    have hi_pos_lt : i_pos < p_i.length := by
      by_contra h; push_neg at h
      rw [List.getElem?_eq_none (by omega)] at hi_pos_u; exact absurd hi_pos_u (by simp)
    have hi_pos1_lt : i_pos + 1 < p_i.length := by
      by_contra h; push_neg at h
      rw [List.getElem?_eq_none (by omega)] at hi_pos_v; exact absurd hi_pos_v (by simp)
    have hpi_u : p_i[i_pos] = u := by
      have := List.getElem?_eq_getElem hi_pos_lt; rw [this] at hi_pos_u
      exact Option.some_injective _ hi_pos_u
    have hpi_v : p_i[i_pos + 1] = v := by
      have := List.getElem?_eq_getElem hi_pos1_lt; rw [this] at hi_pos_v
      exact Option.some_injective _ hi_pos_v
    have hp0 : p_i[0]'(by omega) = N.s := by
      rw [List.head?_eq_getElem?] at hhead_i
      have := List.getElem?_eq_getElem (by omega : 0 < p_i.length)
      rw [this] at hhead_i; exact Option.some_injective _ hhead_i
    intro hv_eq
    have h_same : p_i[i_pos + 1] = p_i[0]'(by omega) := hpi_v.trans (hv_eq.trans hp0.symm)
    have h_ne_idx : i_pos + 1 ≠ 0 := by omega
    exact h_ne_idx (hnodup_i.getElem_inj_iff.mp h_same)
  have hfin_m_v : dirDist (resAdj N (seq.fl m.castSucc)) N.s v ≠ ⊤ :=
    dist_finite_on_path N (seq.fl m.castSucc) p_m hp_m v u hvu_on_m hv_ne_s
  have hdist_m_u : dirDist (resAdj N (seq.fl m.castSucc)) N.s u =
      dirDist (resAdj N (seq.fl m.castSucc)) N.s v + 1 :=
    dist_on_shortest_path N (seq.fl m.castSucc) p_m hp_m v u hvu_on_m hfin_m_v


  have hmono_v : dirDist (resAdj N (seq.fl i.castSucc)) N.s v ≤
      dirDist (resAdj N (seq.fl m.castSucc)) N.s v :=
    vertex_dist_monotone_seq N seq v i.castSucc m.castSucc (by exact_mod_cast him.le)


  have hmono_u : dirDist (resAdj N (seq.fl m.castSucc)) N.s u ≤
      dirDist (resAdj N (seq.fl j.castSucc)) N.s u :=
    vertex_dist_monotone_seq N seq u m.castSucc j.castSucc (by exact_mod_cast hmj)


  calc dirDist (resAdj N (seq.fl i.castSucc)) N.s u + 2
      = dirDist (resAdj N (seq.fl i.castSucc)) N.s v + 1 := by rw [hdist_i_v]; ring
    _ ≤ dirDist (resAdj N (seq.fl m.castSucc)) N.s v + 1 := by gcongr
    _ = dirDist (resAdj N (seq.fl m.castSucc)) N.s u := hdist_m_u.symm
    _ ≤ dirDist (resAdj N (seq.fl j.castSucc)) N.s u := hmono_u

theorem dist_ge_one_of_ne_source
    (N : FlowNetwork V) (fl : STFlow N) (p : List V)
    (hp : IsShortestAugmentingPath N fl p) (u v : V)
    (huv : EdgeOnPath p u v) (hus : u ≠ N.s) :
    (1 : ℕ∞) ≤ dirDist (resAdj N fl) N.s u := by


  unfold dirDist
  by_cases hne : (dirPathLengths (resAdj N fl) N.s u).Nonempty
  · apply le_csInf hne
    intro x hx
    obtain ⟨k, q, hq, hlen, hxeq⟩ := hx
    subst hxeq
    have hk : k ≥ 1 := by
      have := hq.1
      omega
    exact WithTop.coe_le_coe.mpr hk
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp only [hne, sInf_empty]
    exact le_top

theorem bottleneck_edge_bound (N : FlowNetwork V) {k : ℕ}
    (seq : ShortestAugSeq N k) (u v : V) :
    bottleneckCount N seq u v ≤ Fintype.card V / 2 := by

  set B := Finset.filter (fun i : Fin k =>
    ∃ (p : List V) (hp : IsShortestAugmentingPath N (seq.fl i.castSucc) p),
      IsBottleneckEdge N (seq.fl i.castSucc) p hp u v) Finset.univ

  show B.card ≤ Fintype.card V / 2

  by_cases hu : u = N.s
  ·

    subst hu
    suffices hcard1 : B.card ≤ 1 by
      have hn : Fintype.card V ≥ 2 := by
        have hst : N.s ≠ N.t := N.s_ne_t
        have h := Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨N.s, N.t, hst⟩⟩
        omega
      omega
    by_contra h_gt
    push_neg at h_gt

    have ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨p_a, hp_a, hbot_a⟩ := ha
    obtain ⟨p_b, hp_b, hbot_b⟩ := hb
    have hab' : a ≠ b := hab
    rcases lt_or_gt_of_ne hab' with h_lt | h_lt
    · exact source_edge_bottleneck_at_most_once N seq v a b h_lt
        p_a hp_a hbot_a p_b hp_b hbot_b
    · exact source_edge_bottleneck_at_most_once N seq v b a h_lt
        p_b hp_b hbot_b p_a hp_a hbot_a

  ·

    set f : Fin k → ℕ := fun i => (dirDist (resAdj N (seq.fl i.castSucc)) N.s u).toNat

    apply card_le_of_step_bound B f

    · intro i hi
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨p, hp, hbot⟩ := hi
      have huv_on : EdgeOnPath p u v := hbot.1
      have hfin : dirDist (resAdj N (seq.fl i.castSucc)) N.s u ≠ ⊤ :=
        dist_finite_on_path N (seq.fl i.castSucc) p hp u v huv_on hu
      have hge : (1 : ℕ∞) ≤ dirDist (resAdj N (seq.fl i.castSucc)) N.s u :=
        dist_ge_one_of_ne_source N (seq.fl i.castSucc) p hp u v huv_on hu
      show 1 ≤ f i
      simp only [f]
      have heq : dirDist (resAdj N (seq.fl i.castSucc)) N.s u =
          ↑(dirDist (resAdj N (seq.fl i.castSucc)) N.s u).toNat :=
        (ENat.coe_toNat hfin).symm
      rw [heq] at hge
      exact WithTop.coe_le_coe.mp hge

    · intro i hi
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨p, hp, hbot⟩ := hi
      have hfin : dirDist (resAdj N (seq.fl i.castSucc)) N.s u ≠ ⊤ :=
        dist_finite_on_path N (seq.fl i.castSucc) p hp u v hbot.1 hu
      have hle := dirDist_lt_top_le (resAdj N (seq.fl i.castSucc)) N.s u hfin
      show f i ≤ Fintype.card V - 1
      simp only [f]
      have heq : dirDist (resAdj N (seq.fl i.castSucc)) N.s u =
          ↑(dirDist (resAdj N (seq.fl i.castSucc)) N.s u).toNat :=
        (ENat.coe_toNat hfin).symm
      rw [heq] at hle
      exact WithTop.coe_le_coe.mp hle

    · intro i j hi hj hij
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      obtain ⟨p_i, hp_i, hbot_i⟩ := hi
      obtain ⟨p_j, hp_j, hbot_j⟩ := hj
      have hfin_i : dirDist (resAdj N (seq.fl i.castSucc)) N.s u ≠ ⊤ :=
        dist_finite_on_path N (seq.fl i.castSucc) p_i hp_i u v hbot_i.1 hu
      have hfin_j : dirDist (resAdj N (seq.fl j.castSucc)) N.s u ≠ ⊤ :=
        dist_finite_on_path N (seq.fl j.castSucc) p_j hp_j u v hbot_j.1 hu
      have hstep := dist_increase_between_bottlenecks N seq u v i j hij
        p_i hp_i hbot_i p_j hp_j hbot_j
      show f i + 2 ≤ f j
      simp only [f]
      have hi_eq : dirDist (resAdj N (seq.fl i.castSucc)) N.s u =
          ↑(dirDist (resAdj N (seq.fl i.castSucc)) N.s u).toNat :=
        (ENat.coe_toNat hfin_i).symm
      have hj_eq : dirDist (resAdj N (seq.fl j.castSucc)) N.s u =
          ↑(dirDist (resAdj N (seq.fl j.castSucc)) N.s u).toNat :=
        (ENat.coe_toNat hfin_j).symm
      rw [hi_eq, hj_eq] at hstep
      exact WithTop.coe_le_coe.mp (by push_cast at hstep ⊢; exact hstep)

end NetworkFlow
