/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Flow.FlowCutBound

open Finset BigOperators Classical

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def flowSupport (N : FlowNetwork V) (fl : STFlow N) : Finset (V × V) :=
  Finset.univ.filter (fun e => fl.f e.1 e.2 > 0)

structure FlowPath (N : FlowNetwork V) where
  vertices : List V
  nonempty : vertices ≠ []
  starts_at_s : vertices.head nonempty = N.s
  ends_at_t : vertices.getLast nonempty = N.t
  length_ge_two : vertices.length ≥ 2
  nodup : vertices.Nodup

def FlowPath.edges {N : FlowNetwork V} (p : FlowPath N) : List (V × V) :=
  p.vertices.zip p.vertices.tail

def FlowPath.mem_edges {N : FlowNetwork V} (p : FlowPath N) (u v : V) : Prop :=
  (u, v) ∈ p.edges

instance FlowPath.decidable_mem_edges {N : FlowNetwork V} (p : FlowPath N) (u v : V) :
    Decidable (p.mem_edges u v) := by
  unfold mem_edges edges; exact inferInstance

structure FlowDecomposition (N : FlowNetwork V) (fl : STFlow N) where
  f' : STFlow N
  same_value : flowValue N f' = flowValue N fl
  support_sub : flowSupport N f' ⊆ flowSupport N fl
  k : ℕ
  paths : Fin k → FlowPath N
  weights : Fin k → ℝ
  weights_pos : ∀ i, 0 < weights i
  flow_eq : ∀ u v, f'.f u v =
    ∑ i : Fin k, if (paths i).mem_edges u v then weights i else 0
  k_le_support : k ≤ (flowSupport N fl).card

lemma zero_of_flowSupport_empty (N : FlowNetwork V) (fl : STFlow N)
    (hsupp : flowSupport N fl = ∅) : ∀ u v, fl.f u v = 0 := by
  intro u v
  by_contra hne
  have hpos : fl.f u v > 0 := lt_of_le_of_ne (fl.flow_nonneg u v) (Ne.symm hne)
  have hmem : (u, v) ∈ flowSupport N fl := by
    simp only [flowSupport, mem_filter, mem_univ, true_and]; exact hpos
  rw [hsupp] at hmem; simp at hmem

def reachableInSupport (N : FlowNetwork V) (fl : STFlow N) (u v : V) : Prop :=
  Relation.ReflTransGen (fun a b => fl.f a b > 0) u v

noncomputable def reachableSet (N : FlowNetwork V) (fl : STFlow N) : Finset V :=
  Finset.univ.filter (fun v => reachableInSupport N fl N.s v)

lemma s_mem_reachableSet (N : FlowNetwork V) (fl : STFlow N) :
    N.s ∈ reachableSet N fl := by
  simp only [reachableSet, mem_filter, mem_univ, true_and]
  exact Relation.ReflTransGen.refl

lemma reachable_step (N : FlowNetwork V) (fl : STFlow N) (u v : V)
    (hu : u ∈ reachableSet N fl) (hfuv : fl.f u v > 0) :
    v ∈ reachableSet N fl := by
  simp only [reachableSet, mem_filter, mem_univ, true_and] at hu ⊢
  exact Relation.ReflTransGen.tail hu hfuv

lemma flow_zero_across_reachable (N : FlowNetwork V) (fl : STFlow N)
    (u v : V) (hu : u ∈ reachableSet N fl) (hv : v ∉ reachableSet N fl) :
    fl.f u v = 0 := by
  by_contra h
  exact hv (reachable_step N fl u v hu (lt_of_le_of_ne (fl.flow_nonneg u v) (Ne.symm h)))

lemma flowValue_nonpos_of_t_unreachable (N : FlowNetwork V) (fl : STFlow N)
    (ht : N.t ∉ reachableSet N fl) : flowValue N fl ≤ 0 := by
  let S := reachableSet N fl
  have hval : flowValue N fl =
      ∑ v ∈ S, (∑ w : V, fl.f v w - ∑ w : V, fl.f w v) := by
    unfold flowValue
    have hcons : ∀ v ∈ S, v ≠ N.s →
        ∑ w : V, fl.f v w - ∑ w : V, fl.f w v = 0 := by
      intro v _ hvs
      have hvt : v ≠ N.t := fun h => ht (h ▸ ‹v ∈ S›)
      linarith [fl.conservation v hvs hvt]
    rw [← Finset.add_sum_erase S _ (s_mem_reachableSet N fl)]
    simp only [Finset.sum_eq_zero (fun v hv => hcons v (Finset.mem_of_mem_erase hv)
      (Finset.ne_of_mem_erase hv)), add_zero]
  rw [hval]
  have hsplit : ∑ v ∈ S, (∑ w : V, fl.f v w - ∑ w : V, fl.f w v) =
      (∑ v ∈ S, ∑ w ∈ Sᶜ, fl.f v w) + (∑ v ∈ S, ∑ w ∈ S, fl.f v w) -
      (∑ v ∈ S, ∑ w ∈ Sᶜ, fl.f w v) - (∑ v ∈ S, ∑ w ∈ S, fl.f w v) := by
    have split_each : ∀ v, ∑ w : V, fl.f v w = ∑ w ∈ S, fl.f v w + ∑ w ∈ Sᶜ, fl.f v w :=
      fun v => by rw [← Finset.sum_add_sum_compl S]
    have split_each' : ∀ v, ∑ w : V, fl.f w v = ∑ w ∈ S, fl.f w v + ∑ w ∈ Sᶜ, fl.f w v :=
      fun v => by rw [← Finset.sum_add_sum_compl S]
    simp_rw [split_each, split_each', Finset.sum_sub_distrib, Finset.sum_add_distrib]; ring
  have hcross_zero : ∑ v ∈ S, ∑ w ∈ Sᶜ, fl.f v w = 0 :=
    Finset.sum_eq_zero fun v hv =>
      Finset.sum_eq_zero fun w hw =>
        flow_zero_across_reachable N fl v w hv (Finset.mem_compl.mp hw)
  have hback_nonneg : 0 ≤ ∑ v ∈ S, ∑ w ∈ Sᶜ, fl.f w v :=
    Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ => fl.flow_nonneg w v
  linarith [Finset.sum_comm (f := fun v w => fl.f v w) (s := S) (t := S)]

lemma t_reachable_of_pos_value (N : FlowNetwork V) (fl : STFlow N)
    (hpos : 0 < flowValue N fl) : N.t ∈ reachableSet N fl := by
  by_contra ht; linarith [flowValue_nonpos_of_t_unreachable N fl ht]


lemma IsChain_zip_tail {α : Type*} (r : α → α → Prop) (l : List α)
    (hchain : List.IsChain r l) :
    ∀ e ∈ l.zip l.tail, r e.1 e.2 := by
  intro ⟨u, v⟩ he
  induction l with
  | nil => simp at he
  | cons a l' ih =>
    cases l' with
    | nil => simp at he
    | cons b l'' =>
      simp [List.zip, List.tail] at he
      rcases he with ⟨rfl, rfl⟩ | he'
      · cases hchain with | cons_cons hab _ => exact hab
      · exact ih (by cases hchain with | cons_cons _ h => exact h) he'

lemma FlowPath.edges_nonempty {N : FlowNetwork V} (p : FlowPath N) :
    p.edges ≠ [] := by
  intro h
  simp only [FlowPath.edges] at h
  rw [List.zip_eq_nil_iff] at h
  rcases h with h1 | h1
  · exact p.nonempty h1
  · have htail : p.vertices.tail.length = 0 := by simp [h1]
    have hlen := p.length_ge_two
    rw [List.length_tail] at htail
    omega

lemma exists_nodup_chain (R : V → V → Prop) (a b : V) (hab : a ≠ b)
    (hreach : Relation.ReflTransGen R a b) :
    ∃ (l : List V) (hne : l ≠ []),
      List.IsChain R l ∧ l.Nodup ∧
      l.head hne = a ∧ l.getLast hne = b ∧ l.length ≥ 2 := by
  obtain ⟨l, hne, hchain, hhead, hlast⟩ := List.exists_isChain_ne_nil_of_relationReflTransGen hreach
  suffices h : ∀ (n : ℕ) (l : List V) (hne : l ≠ []),
      List.IsChain R l → l.head hne = a → l.getLast hne = b → l.length ≤ n →
      ∃ (l' : List V) (hne' : l' ≠ []),
        List.IsChain R l' ∧ l'.Nodup ∧ l'.head hne' = a ∧ l'.getLast hne' = b ∧ l'.length ≥ 2 from
    h l.length l hne hchain hhead hlast le_rfl
  intro n
  induction n with
  | zero =>
    intro l hne _ _ _ hn
    exact absurd (List.length_pos_of_ne_nil hne) (by omega)
  | succ n ih =>
    intro l hne hchain hhead hlast hlen
    by_cases hnodup : l.Nodup
    · have hlen2 : l.length ≥ 2 := by
        rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
        · exact absurd rfl hne
        · simp [List.head_cons] at hhead hlast
          exact absurd (hhead ▸ hlast : a = b) hab
        · simp
      exact ⟨l, hne, hchain, hnodup, hhead, hlast, hlen2⟩
    · rw [List.nodup_iff_getElem?_ne_getElem?] at hnodup
      push_neg at hnodup
      obtain ⟨i, j, hij, hjl, heq_opt⟩ := hnodup
      have hil : i < l.length := by omega
      have heq' : l[i]'hil = l[j]'hjl := by
        have h1 := List.getElem?_eq_getElem hil
        have h2 := List.getElem?_eq_getElem hjl
        rw [h1, h2] at heq_opt
        exact Option.some_injective _ heq_opt
      have htake_ne : l.take (i + 1) ≠ [] := by
        intro h; have := congr_arg List.length h
        simp [List.length_take, Nat.min_eq_left (by omega : i + 1 ≤ l.length)] at this
      have hne_app : l.take (i + 1) ++ l.drop (j + 1) ≠ [] := by
        intro h; exact htake_ne ((List.append_eq_nil_iff.mp h).1)
      have hchain_app : List.IsChain R (l.take (i + 1) ++ l.drop (j + 1)) :=
        List.IsChain.append (hchain.prefix (List.take_prefix _ _))
          (hchain.suffix (List.drop_suffix _ _))
          (by
            intro x hx y hy
            simp [List.getLast?_eq_getElem?, List.length_take,
                  min_eq_left (show i + 1 ≤ l.length from by omega)] at hx
            simp [List.head?_eq_getElem?] at hy
            subst hx; rw [heq']
            have hj1 : j + 1 < l.length := by
              by_contra h; push_neg at h
              simp [List.getElem?_eq_none (by omega : l.length ≤ j + 1)] at hy
            have hy_val : y = l[j + 1] := by
              rw [List.getElem?_eq_getElem hj1] at hy
              exact (Option.some_injective _ hy).symm
            subst hy_val
            exact (List.isChain_iff_getElem.mp hchain) j hj1)
      have hhead_app : (l.take (i + 1) ++ l.drop (j + 1)).head hne_app = a := by
        rw [List.head_append_of_ne_nil htake_ne]
        cases l with
        | nil => exact absurd rfl hne
        | cons x t => simp [List.take, List.head_cons]; exact hhead
      have hlast_app : (l.take (i + 1) ++ l.drop (j + 1)).getLast hne_app = b := by
        by_cases hdrop : l.drop (j + 1) = []
        · simp [hdrop, List.append_nil]
          rw [List.getLast_take htake_ne]
          simp only [show i + 1 - 1 = i from by omega]
          rw [List.getElem?_eq_getElem hil, Option.getD_some]
          rw [heq']
          have hj_last : j = l.length - 1 := by
            have : (l.drop (j + 1)).length = 0 := by simp [hdrop]
            simp [List.length_drop] at this; omega
          have : l[j]'hjl = l.getLast hne := by
            simp [List.getLast_eq_getElem]
            congr 1
          rw [this, hlast]
        · rw [List.getLast_append_of_ne_nil _ hdrop, List.getLast_drop hdrop]
          exact hlast
      have hlen_app : (l.take (i + 1) ++ l.drop (j + 1)).length ≤ n := by
        simp [List.length_append, List.length_take, List.length_drop,
              Nat.min_eq_left (by omega : i + 1 ≤ l.length)]
        omega
      exact ih _ hne_app hchain_app hhead_app hlast_app hlen_app

lemma exists_flow_path_of_pos_value (N : FlowNetwork V) (fl : STFlow N)
    (hval : 0 < flowValue N fl) :
    ∃ (p : FlowPath N), ∀ e ∈ p.edges, fl.f e.1 e.2 > 0 := by

  have hreach := t_reachable_of_pos_value N fl hval
  simp only [reachableSet, mem_filter, mem_univ, true_and, reachableInSupport] at hreach

  obtain ⟨l, hne, hchain, hnodup, hhead, hlast, hlen2⟩ :=
    exists_nodup_chain (fun a b => fl.f a b > 0) N.s N.t N.s_ne_t hreach

  exact ⟨⟨l, hne, hhead, hlast, hlen2, hnodup⟩,
    IsChain_zip_tail _ l hchain⟩

lemma remove_cycle_step (N : FlowNetwork V) (fl : STFlow N)
    (hsupp : flowSupport N fl ≠ ∅)
    (hval : flowValue N fl = 0) :
    ∃ fl' : STFlow N,
      flowValue N fl' = flowValue N fl ∧
      flowSupport N fl' ⊂ flowSupport N fl := by

  have outflow_exists : ∀ v : V, (0 < ∑ u : V, fl.f u v) → ∃ w : V, 0 < fl.f v w := by
    intro v hv
    suffices h_out_pos : 0 < ∑ u : V, fl.f v u by
      by_contra hall; push_neg at hall
      linarith [le_antisymm (Finset.sum_nonpos (f := fl.f v) (s := univ) (fun w _ => hall w))
        (Finset.sum_nonneg (f := fl.f v) (s := univ) (fun w _ => fl.flow_nonneg v w))]
    by_cases hvs : v = N.s
    · subst hvs; unfold flowValue at hval; linarith
    · by_cases hvt : v = N.t
      · have htotal : ∑ w : V, ∑ u : V, fl.f u w = ∑ w : V, ∑ u : V, fl.f w u := by
          conv_lhs => rw [Finset.sum_comm]
        have hlhs : ∑ w : V, ∑ u : V, fl.f u w =
            ∑ u, fl.f u N.s + ∑ u, fl.f u N.t +
            ∑ w ∈ (univ.erase N.s).erase N.t, ∑ u, fl.f u w := by
          have h1 := (Finset.add_sum_erase (univ : Finset V)
            (fun w => ∑ u, fl.f u w) (mem_univ N.s)).symm
          have ht_mem : N.t ∈ univ.erase N.s :=
            mem_erase.mpr ⟨N.s_ne_t.symm, mem_univ N.t⟩
          linarith [(Finset.add_sum_erase _ (fun w => ∑ u, fl.f u w) ht_mem).symm]
        have hrhs : ∑ w : V, ∑ u : V, fl.f w u =
            ∑ u, fl.f N.s u + ∑ u, fl.f N.t u +
            ∑ w ∈ (univ.erase N.s).erase N.t, ∑ u, fl.f w u := by
          have h1 := (Finset.add_sum_erase (univ : Finset V)
            (fun w => ∑ u, fl.f w u) (mem_univ N.s)).symm
          have ht_mem : N.t ∈ univ.erase N.s :=
            mem_erase.mpr ⟨N.s_ne_t.symm, mem_univ N.t⟩
          linarith [(Finset.add_sum_erase _ (fun w => ∑ u, fl.f w u) ht_mem).symm]
        have hrest : ∑ w ∈ (univ.erase N.s).erase N.t, ∑ u : V, fl.f u w =
            ∑ w ∈ (univ.erase N.s).erase N.t, ∑ u : V, fl.f w u :=
          Finset.sum_congr rfl fun w hw => fl.conservation w
            (by simp [mem_erase] at hw; exact hw.2) (by simp [mem_erase] at hw; exact hw.1)
        have h_t_bal : ∑ u : V, fl.f u N.t = ∑ u : V, fl.f N.t u := by
          unfold flowValue at hval; linarith
        subst hvt; linarith
      · linarith [fl.conservation v hvs hvt]

  obtain ⟨⟨a, b⟩, hab⟩ := Finset.nonempty_of_ne_empty hsupp
  simp only [flowSupport, mem_filter, mem_univ, true_and] at hab
  have hb_in : 0 < ∑ u : V, fl.f u b :=
    lt_of_lt_of_le hab (Finset.single_le_sum (fun u _ => fl.flow_nonneg u b) (mem_univ a))

  let next : V → V := fun v => if h : ∃ w : V, 0 < fl.f v w then h.choose else v
  have hnext_pos : ∀ v, (∃ w, 0 < fl.f v w) → 0 < fl.f v (next v) := by
    intro v h; simp only [next, dif_pos h]; exact h.choose_spec
  let walk : ℕ → V := fun n => next^[n] b
  have hwalk_succ : ∀ n, walk (n + 1) = next (walk n) :=
    fun n => Function.iterate_succ_apply' next n b

  have hwalk_pos : ∀ k : ℕ, 0 < fl.f (walk k) (walk (k + 1)) := by
    intro k; rw [show walk (k + 1) = next (walk k) from hwalk_succ k]
    apply hnext_pos; apply outflow_exists
    induction k with
    | zero => simp only [walk, Function.iterate_zero, id_eq]; exact hb_in
    | succ k ih =>
      have hprev : 0 < fl.f (walk k) (walk (k + 1)) := by
        rw [hwalk_succ k]; exact hnext_pos _ (outflow_exists _ ih)
      exact lt_of_lt_of_le hprev
        (Finset.single_le_sum (fun u _ => fl.flow_nonneg u (walk (k + 1))) (mem_univ (walk k)))

  obtain ⟨i, j, hij, hcycle_eq, hinj⟩ :
      ∃ i j : ℕ, i < j ∧ walk i = walk j ∧
        (∀ a b, i ≤ a → a < j → i ≤ b → b < j → walk a = walk b → a = b) := by

    have hcard : Fintype.card V < Fintype.card (Fin (Fintype.card V + 1)) := by simp
    obtain ⟨p, q, hpq, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (Fintype.card V + 1) => walk k.val) hcard
    have ⟨i₀, j₀, hij₀, hcyc₀⟩ : ∃ i₀ j₀ : ℕ, i₀ < j₀ ∧ walk i₀ = walk j₀ := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hpq) with h | h
      · exact ⟨p.val, q.val, h, heq⟩
      · exact ⟨q.val, p.val, h, heq.symm⟩

    let P : ℕ → Prop := fun d => ∃ i j : ℕ, i < j ∧ j - i = d + 1 ∧ walk i = walk j
    have hPex : ∃ d, P d := ⟨j₀ - i₀ - 1, i₀, j₀, hij₀, by omega, hcyc₀⟩
    obtain ⟨i, j, hij', hji, hcyc'⟩ := Nat.find_spec hPex
    refine ⟨i, j, hij', hcyc', ?_⟩
    intro a b ha haj hb hbj hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with halt | halt
    · exact Nat.find_min hPex (show b - a - 1 < Nat.find hPex from by omega)
        ⟨a, b, halt, by omega, hab⟩
    · exact Nat.find_min hPex (show a - b - 1 < Nat.find hPex from by omega)
        ⟨b, a, halt, by omega, hab.symm⟩


  let cycleEdges : Finset (V × V) :=
    (Finset.range (j - i)).image (fun k => (walk (i + k), walk (i + k + 1)))
  have hcycle_ne : cycleEdges.Nonempty := by
    exact ⟨(walk i, walk (i + 1)), Finset.mem_image.mpr
      ⟨0, Finset.mem_range.mpr (by omega), by simp⟩⟩
  have hcycle_pos : ∀ e ∈ cycleEdges, 0 < fl.f e.1 e.2 := by
    intro ⟨u, v⟩ he
    simp only [cycleEdges, Finset.mem_image, Finset.mem_range] at he
    obtain ⟨k, hk, hkuv⟩ := he
    have := hwalk_pos (i + k)
    have h1 : u = walk (i + k) := (Prod.mk.inj hkuv).1.symm
    have h2 : v = walk (i + k + 1) := (Prod.mk.inj hkuv).2.symm
    simp only [h1, h2]; exact this
  let w := cycleEdges.inf' hcycle_ne (fun e => fl.f e.1 e.2)
  have hw_pos : 0 < w := by rw [Finset.lt_inf'_iff]; exact hcycle_pos
  have hw_le : ∀ e ∈ cycleEdges, w ≤ fl.f e.1 e.2 := fun e he => Finset.inf'_le _ he
  obtain ⟨ebot, hebot_mem, hebot_eq⟩ :=
    Finset.exists_mem_eq_inf' hcycle_ne (fun e => fl.f e.1 e.2)

  have hfl'_nonneg : ∀ u v, 0 ≤ fl.f u v - if (u, v) ∈ cycleEdges then w else 0 := by
    intro u v; split_ifs with h
    · linarith [hw_le (u, v) h]
    · linarith [fl.flow_nonneg u v]
  have hfl'_cap : ∀ u v, fl.f u v - (if (u, v) ∈ cycleEdges then w else 0) ≤ N.cap u v := by
    intro u v; split_ifs with h
    · linarith [fl.flow_cap u v]
    · linarith [fl.flow_cap u v]


  have hcycle_balance : ∀ v : V, ∑ u : V, (if (u, v) ∈ cycleEdges then (1:ℝ) else 0) =
      ∑ u : V, (if (v, u) ∈ cycleEdges then (1:ℝ) else 0) := by
    intro v
    simp only [Finset.sum_boole, Nat.cast_inj]

    by_cases hv : ∃ m, m < j - i ∧ walk (i + m) = v
    · obtain ⟨m, hm, hvm⟩ := hv
      have hright : (filter (fun u => (v, u) ∈ cycleEdges) univ).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨walk (i + m + 1), ?_⟩
        ext u; simp only [mem_filter, mem_univ, true_and, mem_singleton,
          cycleEdges, mem_image, mem_range]
        constructor
        · rintro ⟨k, hk, hkuv⟩
          have hfst := (Prod.mk.inj hkuv).1
          have hsnd := (Prod.mk.inj hkuv).2
          have := hinj (i+k) (i+m) (by omega) (by omega) (by omega) (by omega)
            (hfst.trans hvm.symm)
          rw [← hsnd]; congr 1; omega
        · intro hu; subst hu
          exact ⟨m, hm, by simp [hvm.symm]⟩
      have hleft : (filter (fun u => (u, v) ∈ cycleEdges) univ).card = 1 := by
        rw [Finset.card_eq_one]
        let pred := if m = 0 then walk (j - 1) else walk (i + m - 1)
        refine ⟨pred, ?_⟩
        ext u; simp only [mem_filter, mem_univ, true_and, mem_singleton,
          cycleEdges, mem_image, mem_range]
        constructor
        · rintro ⟨k, hk, hkuv⟩
          have hfst := (Prod.mk.inj hkuv).1
          have hsnd := (Prod.mk.inj hkuv).2
          by_cases hkj : i + k + 1 = j
          · have hm0 : m = 0 := by
              have h1 : walk i = v := by
                have h3 : walk j = v := by rw [← hkj]; exact hsnd
                exact hcycle_eq.trans h3
              have := hinj i (i+m) (le_refl _) (by omega) (by omega) (by omega)
                (h1.trans hvm.symm)
              omega
            simp only [pred, hm0, ite_true, ← hfst]; congr 1; omega
          · have hlt : i + k + 1 < j := by omega
            have := hinj (i+k+1) (i+m) (by omega) hlt (by omega) (by omega)
              (hsnd.trans hvm.symm)
            have hm_pos : m ≠ 0 := by omega
            simp only [pred, hm_pos, ite_false, ← hfst]; congr 1; omega
        · intro hu; simp only [pred] at hu
          split_ifs at hu with hm0
          · subst hu
            refine ⟨j - i - 1, by omega, ?_⟩
            have h1 : walk (i + (j - i - 1)) = walk (j - 1) := by congr 1; omega
            have h2 : walk (i + (j - i - 1) + 1) = v := by
              rw [show i + (j - i - 1) + 1 = j from by omega]
              have : walk j = walk i := hcycle_eq.symm
              rw [this, ← hvm, hm0]; ring_nf
            exact Prod.ext h1 h2
          · subst hu
            refine ⟨m - 1, by omega, ?_⟩
            have h1 : walk (i + (m - 1)) = walk (i + m - 1) := by congr 1; omega
            have h2 : walk (i + (m - 1) + 1) = v := by
              rw [show i + (m - 1) + 1 = i + m from by omega]; exact hvm
            exact Prod.ext h1 h2
      linarith
    · push_neg at hv
      have hleft : (filter (fun u => (u, v) ∈ cycleEdges) univ).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro u _
        simp only [cycleEdges, mem_image, mem_range]
        rintro ⟨k, hk, hkuv⟩
        have hsnd := (Prod.mk.inj hkuv).2
        by_cases hkj : i + k + 1 = j
        · have : walk i = v := hcycle_eq.trans (by rw [← hkj]; exact hsnd)
          exact hv 0 (by omega) (by rwa [show i + 0 = i from by omega])
        · exact hv (k+1) (by omega) hsnd
      have hright : (filter (fun u => (v, u) ∈ cycleEdges) univ).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro u _
        simp only [cycleEdges, mem_image, mem_range]
        rintro ⟨k, hk, hkuv⟩
        exact hv k hk (Prod.mk.inj hkuv).1
      linarith

  have hfl'_cons : ∀ v, v ≠ N.s → v ≠ N.t →
      ∑ u : V, (fl.f u v - if (u, v) ∈ cycleEdges then w else 0) =
      ∑ u : V, (fl.f v u - if (v, u) ∈ cycleEdges then w else 0) := by
    intro v hvs hvt
    simp_rw [Finset.sum_sub_distrib]
    have hcons := fl.conservation v hvs hvt
    suffices hind : ∑ u : V, (if (u, v) ∈ cycleEdges then w else (0 : ℝ)) =
        ∑ u : V, (if (v, u) ∈ cycleEdges then w else (0 : ℝ)) by linarith
    have h1 : ∀ u, (if (u, v) ∈ cycleEdges then w else (0:ℝ)) =
        w * (if (u, v) ∈ cycleEdges then 1 else 0) := by intro u; split_ifs <;> ring
    have h2 : ∀ u, (if (v, u) ∈ cycleEdges then w else (0:ℝ)) =
        w * (if (v, u) ∈ cycleEdges then 1 else 0) := by intro u; split_ifs <;> ring
    simp_rw [h1, h2, ← Finset.mul_sum]; congr 1; exact hcycle_balance v
  let fl' : STFlow N := ⟨fun u v => fl.f u v - if (u, v) ∈ cycleEdges then w else 0,
    hfl'_nonneg, hfl'_cap, hfl'_cons⟩
  refine ⟨fl', ?_, ?_⟩
  ·
    unfold flowValue; simp only [fl']
    simp_rw [Finset.sum_sub_distrib]
    have h1 : ∀ u, (if (N.s, u) ∈ cycleEdges then w else (0:ℝ)) =
        w * (if (N.s, u) ∈ cycleEdges then 1 else 0) := by intro u; split_ifs <;> ring
    have h2 : ∀ u, (if (u, N.s) ∈ cycleEdges then w else (0:ℝ)) =
        w * (if (u, N.s) ∈ cycleEdges then 1 else 0) := by intro u; split_ifs <;> ring
    simp_rw [h1, h2, ← Finset.mul_sum]; nlinarith [hcycle_balance N.s]
  ·
    apply (Finset.subset_iff.mpr ?_).ssubset_of_ne ?_
    · intro ⟨u, v⟩ hmem
      simp only [flowSupport, mem_filter, mem_univ, true_and] at hmem ⊢
      simp only [fl'] at hmem
      have hge : (0 : ℝ) ≤ if (u, v) ∈ cycleEdges then w else 0 := by split_ifs <;> linarith
      linarith
    · intro heq
      have hbot_in_fl : (ebot.1, ebot.2) ∈ flowSupport N fl := by
        simp only [flowSupport, mem_filter, mem_univ, true_and]; linarith [hcycle_pos ebot hebot_mem]
      have hbot_not_in_fl' : (ebot.1, ebot.2) ∉ flowSupport N fl' := by
        simp only [flowSupport, mem_filter, mem_univ, true_and, not_lt, fl']
        simp only [hebot_mem, ite_true]; linarith [hebot_eq.symm]
      rw [← heq] at hbot_in_fl; exact hbot_not_in_fl' hbot_in_fl

lemma decompose_one_step (N : FlowNetwork V) (fl : STFlow N)
    (hval : 0 < flowValue N fl) :
    ∃ (p : FlowPath N) (w : ℝ) (fl' : STFlow N),
      0 < w ∧
      (∀ u v, fl.f u v = fl'.f u v + if p.mem_edges u v then w else 0) ∧
      flowSupport N fl' ⊂ flowSupport N fl := by

  obtain ⟨p, hp_edges⟩ := exists_flow_path_of_pos_value N fl hval

  let edgeSet : Finset (V × V) := p.edges.toFinset
  have hne' : edgeSet.Nonempty := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ p.edges_nonempty
    exact ⟨x, List.mem_toFinset.mpr hx⟩
  let w := edgeSet.inf' hne' (fun e => fl.f e.1 e.2)

  have hw_pos : 0 < w := by
    rw [Finset.lt_inf'_iff]
    intro e he
    exact hp_edges e (List.mem_toFinset.mp he)

  have hw_le : ∀ e ∈ p.edges, w ≤ fl.f e.1 e.2 :=
    fun e he => Finset.inf'_le _ (List.mem_toFinset.mpr he)

  obtain ⟨ebot, hebot_mem, hebot_eq⟩ := Finset.exists_mem_eq_inf' hne' (fun e => fl.f e.1 e.2)
  have hebot_in_edges : ebot ∈ p.edges := List.mem_toFinset.mp hebot_mem

  have hfl'_nonneg : ∀ u v, 0 ≤ fl.f u v - if p.mem_edges u v then w else 0 := by
    intro u v; split_ifs with h
    · linarith [hw_le (u, v) h]
    · linarith [fl.flow_nonneg u v]
  have hfl'_cap : ∀ u v, fl.f u v - (if p.mem_edges u v then w else 0) ≤ N.cap u v := by
    intro u v; split_ifs
    · linarith [fl.flow_cap u v]
    · linarith [fl.flow_cap u v]
  have hfl'_cons : ∀ v, v ≠ N.s → v ≠ N.t →
      ∑ u : V, (fl.f u v - if p.mem_edges u v then w else 0) =
      ∑ u : V, (fl.f v u - if p.mem_edges v u then w else 0) := by
    intro v hvs hvt
    simp_rw [Finset.sum_sub_distrib]
    have hcons := fl.conservation v hvs hvt

    suffices hind : ∑ u : V, (if p.mem_edges u v then w else (0 : ℝ)) =
        ∑ u : V, (if p.mem_edges v u then w else (0 : ℝ)) by linarith

    show ∑ u : V, (if (u, v) ∈ p.vertices.zip p.vertices.tail then w else (0 : ℝ)) =
        ∑ u : V, (if (v, u) ∈ p.vertices.zip p.vertices.tail then w else (0 : ℝ))

    by_cases hv_mem : v ∈ p.vertices
    ·
      have hv_tail : v ∈ p.vertices.tail := by
        cases hv : p.vertices with
        | nil => exact absurd hv p.nonempty
        | cons a t =>
          simp only [List.tail_cons]
          have ha_eq : a = N.s := by
            have h := p.starts_at_s
            simp [hv, List.head_cons] at h; exact h
          have hv_in : v ∈ a :: t := hv ▸ hv_mem
          exact (List.mem_cons.mp hv_in).resolve_left (by rw [ha_eq]; exact hvs)
      have hv_dropLast : v ∈ p.vertices.dropLast :=
        List.mem_dropLast_of_mem_of_ne_getLast hv_mem (by rw [p.ends_at_t]; exact hvt)

      have hex_fst : ∃ u₀, (u₀, v) ∈ p.vertices.zip p.vertices.tail := by
        rw [List.mem_iff_getElem] at hv_tail
        obtain ⟨i, hi_len, hiv⟩ := hv_tail
        have hi_l : i < p.vertices.length := by
          have := List.length_tail (l := p.vertices); omega
        have hi_zip : i < (p.vertices.zip p.vertices.tail).length := by
          have := List.length_tail (l := p.vertices); rw [List.length_zip]; omega
        exact ⟨p.vertices[i]'hi_l, List.mem_iff_getElem.mpr
          ⟨i, hi_zip, by rw [List.getElem_zip (h := hi_zip), hiv]⟩⟩
      have huniq_fst : ∀ u₁ u₂, (u₁, v) ∈ p.vertices.zip p.vertices.tail →
          (u₂, v) ∈ p.vertices.zip p.vertices.tail → u₁ = u₂ := by
        intro u₁ u₂ h1 h2
        rw [List.mem_iff_getElem] at h1 h2
        obtain ⟨i₁, hi₁_len, hi₁⟩ := h1
        obtain ⟨i₂, hi₂_len, hi₂⟩ := h2
        have hlt := List.length_tail (l := p.vertices)
        have hi₁_l' : i₁ + 1 < p.vertices.length := by rw [List.length_zip] at hi₁_len; omega
        have hi₂_l' : i₂ + 1 < p.vertices.length := by rw [List.length_zip] at hi₂_len; omega
        rw [List.getElem_zip] at hi₁ hi₂
        have hv₁ : p.vertices[i₁ + 1]'hi₁_l' = v := by
          have := congrArg Prod.snd hi₁; simp [List.getElem_tail] at this; exact this
        have hv₂ : p.vertices[i₂ + 1]'hi₂_l' = v := by
          have := congrArg Prod.snd hi₂; simp [List.getElem_tail] at this; exact this
        have heq_idx : i₁ + 1 = i₂ + 1 :=
          (p.nodup.getElem_inj_iff (hi := hi₁_l') (hj := hi₂_l')).mp (hv₁.trans hv₂.symm)
        have hu₁ : p.vertices[i₁]'(by omega) = u₁ := by
          have := congrArg Prod.fst hi₁; simpa using this
        have hu₂ : p.vertices[i₂]'(by omega) = u₂ := by
          have := congrArg Prod.fst hi₂; simpa using this
        rw [← hu₁, ← hu₂]; congr 1; omega

      have hex_snd : ∃ u₀, (v, u₀) ∈ p.vertices.zip p.vertices.tail := by
        rw [List.mem_iff_getElem] at hv_dropLast
        obtain ⟨i, hi_len, hiv⟩ := hv_dropLast
        have hlen_dl : p.vertices.dropLast.length = p.vertices.length - 1 := List.length_dropLast
        have hi_l : i < p.vertices.length := by omega
        have hi_tail : i < p.vertices.tail.length := by
          have := List.length_tail (l := p.vertices); omega
        have hi_zip : i < (p.vertices.zip p.vertices.tail).length := by
          have := List.length_tail (l := p.vertices); rw [List.length_zip]; omega
        refine ⟨p.vertices.tail[i]'hi_tail, List.mem_iff_getElem.mpr ⟨i, hi_zip, ?_⟩⟩
        rw [List.getElem_zip (h := hi_zip)]
        congr 1
        rw [List.getElem_dropLast] at hiv
        exact hiv
      have huniq_snd : ∀ u₁ u₂, (v, u₁) ∈ p.vertices.zip p.vertices.tail →
          (v, u₂) ∈ p.vertices.zip p.vertices.tail → u₁ = u₂ := by
        intro u₁ u₂ h1 h2
        rw [List.mem_iff_getElem] at h1 h2
        obtain ⟨i₁, hi₁_len, hi₁⟩ := h1
        obtain ⟨i₂, hi₂_len, hi₂⟩ := h2
        have hlt := List.length_tail (l := p.vertices)
        have hi₁_l : i₁ < p.vertices.length := by rw [List.length_zip] at hi₁_len; omega
        have hi₂_l : i₂ < p.vertices.length := by rw [List.length_zip] at hi₂_len; omega
        have hi₁_l' : i₁ + 1 < p.vertices.length := by rw [List.length_zip] at hi₁_len; omega
        have hi₂_l' : i₂ + 1 < p.vertices.length := by rw [List.length_zip] at hi₂_len; omega
        rw [List.getElem_zip] at hi₁ hi₂
        have hv₁ : p.vertices[i₁]'hi₁_l = v := by
          have := congrArg Prod.fst hi₁; simpa using this
        have hv₂ : p.vertices[i₂]'hi₂_l = v := by
          have := congrArg Prod.fst hi₂; simpa using this
        have heq_idx : i₁ = i₂ :=
          (p.nodup.getElem_inj_iff (hi := hi₁_l) (hj := hi₂_l)).mp (hv₁.trans hv₂.symm)
        have hu₁ : p.vertices[i₁ + 1]'hi₁_l' = u₁ := by
          have := congrArg Prod.snd hi₁; simp [List.getElem_tail] at this; exact this
        have hu₂ : p.vertices[i₂ + 1]'hi₂_l' = u₂ := by
          have := congrArg Prod.snd hi₂; simp [List.getElem_tail] at this; exact this
        rw [← hu₁, ← hu₂]; congr 1; omega

      obtain ⟨u₁, hu₁_mem⟩ := hex_fst
      obtain ⟨u₂, hu₂_mem⟩ := hex_snd
      have lhs_eq : ∑ u : V, (if (u, v) ∈ p.vertices.zip p.vertices.tail then w else (0:ℝ)) = w := by
        have hiff : ∀ u : V, ((u, v) ∈ p.vertices.zip p.vertices.tail) ↔ (u = u₁) :=
          fun u => ⟨fun h => huniq_fst u u₁ h hu₁_mem, fun h => h ▸ hu₁_mem⟩
        simp_rw [show ∀ u, (u, v) ∈ p.vertices.zip p.vertices.tail ↔ u = u₁ from hiff]
        simp [Finset.sum_ite_eq']
      have rhs_eq : ∑ u : V, (if (v, u) ∈ p.vertices.zip p.vertices.tail then w else (0:ℝ)) = w := by
        have hiff : ∀ u : V, ((v, u) ∈ p.vertices.zip p.vertices.tail) ↔ (u = u₂) :=
          fun u => ⟨fun h => huniq_snd u u₂ h hu₂_mem, fun h => h ▸ hu₂_mem⟩
        simp_rw [show ∀ u, (v, u) ∈ p.vertices.zip p.vertices.tail ↔ u = u₂ from hiff]
        simp [Finset.sum_ite_eq']
      linarith
    ·
      have h1 : ∀ u, (u, v) ∉ p.vertices.zip p.vertices.tail :=
        fun u h => hv_mem (List.mem_of_mem_tail (List.of_mem_zip h).2)
      have h2 : ∀ u, (v, u) ∉ p.vertices.zip p.vertices.tail :=
        fun u h => hv_mem (List.of_mem_zip h).1
      simp [show ∀ u, (u, v) ∈ p.vertices.zip p.vertices.tail ↔ False from
            fun u => ⟨fun h => h1 u h, False.elim⟩,
            show ∀ u, (v, u) ∈ p.vertices.zip p.vertices.tail ↔ False from
            fun u => ⟨fun h => h2 u h, False.elim⟩]
  let fl' : STFlow N := ⟨fun u v => fl.f u v - if p.mem_edges u v then w else 0,
    hfl'_nonneg, hfl'_cap, hfl'_cons⟩

  refine ⟨p, w, fl', hw_pos, ?_, ?_⟩
  ·
    intro u v; simp only [fl']; ring
  ·
    apply (Finset.subset_iff.mpr ?_).ssubset_of_ne ?_
    ·
      intro ⟨u, v⟩ hmem
      simp only [flowSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
      simp only [fl'] at hmem
      have hge : (0 : ℝ) ≤ if p.mem_edges u v then w else 0 := by
        split_ifs <;> linarith
      linarith
    ·
      intro heq
      have hbot_in_fl : (ebot.1, ebot.2) ∈ flowSupport N fl := by
        simp only [flowSupport, Finset.mem_filter, Finset.mem_univ, true_and]
        linarith [hp_edges ebot hebot_in_edges]
      have hbot_not_in_fl' : (ebot.1, ebot.2) ∉ flowSupport N fl' := by
        simp only [flowSupport, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, fl']
        have hmem : p.mem_edges ebot.1 ebot.2 := hebot_in_edges
        simp only [hmem, ite_true]
        linarith [hebot_eq.symm]
      rw [← heq] at hbot_in_fl
      exact hbot_not_in_fl' hbot_in_fl




end NetworkFlow
