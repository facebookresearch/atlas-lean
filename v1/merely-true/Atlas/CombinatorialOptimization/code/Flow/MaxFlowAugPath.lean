/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Flow.MaxFlowMinCut
import Atlas.CombinatorialOptimization.code.Flow.LargeAugPath

open Finset BigOperators Classical

noncomputable section

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem isMaxFlow_of_noAugmentingPath (N : FlowNetwork V) (fl : STFlow N)
    (hmax : NoAugmentingPath N fl) : IsMaxFlow N fl := by
  obtain ⟨C, hC⟩ := max_flow_min_cut N fl hmax
  intro fl'
  calc flowValue N fl' ≤ cutCapacity N C := flow_le_cut N fl' C
    _ = flowValue N fl := hC.symm

def IsPathEdge (l : List V) (u v : V) : Prop :=
  ∃ i : Fin (l.length - 1), l[i.val]'(by omega) = u ∧ l[i.val + 1]'(by omega) = v

private instance (l : List V) (u v : V) : Decidable (IsPathEdge l u v) :=
  Fintype.decidableExistsFintype

theorem general_path_augment
    (N : FlowNetwork V) (fl : STFlow N)
    (l : List V) (hne : l ≠ [])
    (hchain : List.IsChain (resAdj' N fl) l)
    (hnodup : l.Nodup) (hlen : l.length ≥ 2)
    (hhead : l.head hne = N.s)
    (hlast : l.getLast hne = N.t) :
    ∃ fl' : STFlow N, flowValue N fl < flowValue N fl' := by

  have hchain_idx : ∀ i (hi : i + 1 < l.length),
      resCap' N fl (l[i]'(by omega)) (l[i+1]'(by omega)) > 0 := by
    intro i hi
    exact (List.isChain_iff_getElem.mp hchain) i hi
  have hfirst : resCap' N fl (l[0]'(by omega)) (l[1]'(by omega)) > 0 :=
    hchain_idx 0 (by omega)

  have hfin_ne : (Finset.univ : Finset (Fin (l.length - 1))).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set δ := (Finset.univ : Finset (Fin (l.length - 1))).inf' hfin_ne
    (fun i => resCap' N fl (l[i.val]'(by omega)) (l[i.val + 1]'(by omega))) / 2
  have hδ_pos : δ > 0 := by
    simp only [δ]
    apply div_pos
    · rw [Finset.lt_inf'_iff]
      intro i _
      exact hchain_idx i.val (by omega)
    · norm_num
  have hδ_le : ∀ i (hi : i + 1 < l.length),
      δ ≤ resCap' N fl (l[i]'(by omega)) (l[i+1]'(by omega)) := by
    intro i hi
    have h := Finset.inf'_le
      (fun j : Fin (l.length - 1) => resCap' N fl (l[j.val]'(by omega)) (l[j.val + 1]'(by omega)))
      (Finset.mem_univ (⟨i, by omega⟩ : Fin (l.length - 1)))
    simp only [δ]
    linarith [hchain_idx i hi]


  have hl0 : l[0]'(by omega) = N.s := by
    conv_lhs => rw [show l[0]'(by omega) = l.head hne from by simp [List.head_eq_getElem]]
    exact hhead
  have hln : l[l.length - 1]'(by omega) = N.t := by
    conv_lhs => rw [show l[l.length - 1]'(by omega) = l.getLast hne from by
      simp [List.getLast_eq_getElem]]
    exact hlast

  set f' : V → V → ℝ := fun u v =>
    if IsPathEdge l u v then
      fl.f u v + min δ (N.cap u v - fl.f u v)
    else if IsPathEdge l v u then
      fl.f u v - (δ - min δ (N.cap v u - fl.f v u))
    else
      fl.f u v
  have hf'_eq : ∀ u v, f' u v =
      if IsPathEdge l u v then fl.f u v + min δ (N.cap u v - fl.f u v)
      else if IsPathEdge l v u then fl.f u v - (δ - min δ (N.cap v u - fl.f v u))
      else fl.f u v := fun u v => rfl

  have hnodup_disjoint : ∀ u v, ¬(IsPathEdge l u v ∧ IsPathEdge l v u) := by
    intro u v ⟨⟨⟨i, hi⟩, hiu, hiv⟩, ⟨⟨j, hj⟩, hjv, hju⟩⟩
    have h1 : (⟨i, by omega⟩ : Fin l.length) = ⟨j + 1, by omega⟩ := by
      apply (hnodup.get_inj_iff).mp
      simp [List.get_eq_getElem, hiu, hju]
    have h2 : (⟨i + 1, by omega⟩ : Fin l.length) = ⟨j, by omega⟩ := by
      apply (hnodup.get_inj_iff).mp
      simp [List.get_eq_getElem, hiv, hjv]
    simp at h1 h2; omega

  refine ⟨⟨f', ?_, ?_, ?_⟩, ?_⟩
  ·
    intro u v; rw [hf'_eq]
    split_ifs with hfwd hrev
    ·

      have hf := fl.flow_nonneg u v
      have hcf := fl.flow_cap u v
      have : min δ (N.cap u v - fl.f u v) ≥ 0 := by
        apply le_min hδ_pos.le
        linarith
      linarith
    ·

      obtain ⟨⟨j, hj⟩, hjv, hju⟩ := hrev
      have hrc := hδ_le j (by omega)
      unfold resCap' at hrc


      have hmin_le : min δ (N.cap v u - fl.f v u) ≤ N.cap v u - fl.f v u := min_le_right _ _


      suffices h : fl.f u v ≥ δ - min δ (N.cap v u - fl.f v u) by linarith
      by_cases hcase : N.cap v u - fl.f v u ≥ δ
      · have : min δ (N.cap v u - fl.f v u) = δ := min_eq_left hcase
        rw [this]; linarith [fl.flow_nonneg u v]
      · push_neg at hcase
        have : min δ (N.cap v u - fl.f v u) = N.cap v u - fl.f v u :=
          min_eq_right (le_of_lt hcase)
        rw [this]


        have hrc2 : δ ≤ N.cap v u - fl.f v u + fl.f u v := by
          convert hrc using 2 <;> simp [hjv, hju]
        linarith
    · exact fl.flow_nonneg u v
  ·
    intro u v; rw [hf'_eq]
    split_ifs with hfwd hrev
    ·
      have := min_le_right δ (N.cap u v - fl.f u v)
      linarith [fl.flow_cap u v]
    ·

      have hmin_le : min δ (N.cap v u - fl.f v u) ≤ δ := min_le_left _ _
      linarith [fl.flow_cap u v]
    · exact fl.flow_cap u v
  ·
    intro v hvs hvt


    suffices hsuff : (∑ u : V, f' u v) - (∑ u : V, fl.f u v) =
        (∑ u : V, f' v u) - (∑ u : V, fl.f v u) by
      linarith [fl.conservation v hvs hvt]

    have hlhs : (∑ u : V, f' u v) - (∑ u : V, fl.f u v) = ∑ u : V, (f' u v - fl.f u v) := by
      rw [← Finset.sum_sub_distrib]
    have hrhs : (∑ u : V, f' v u) - (∑ u : V, fl.f v u) = ∑ u : V, (f' v u - fl.f v u) := by
      rw [← Finset.sum_sub_distrib]
    rw [hlhs, hrhs]


    have hdiff_in : ∀ u, f' u v - fl.f u v =
        if IsPathEdge l u v then min δ (N.cap u v - fl.f u v)
        else if IsPathEdge l v u then -(δ - min δ (N.cap v u - fl.f v u))
        else 0 := by
      intro u; rw [hf'_eq]; split_ifs <;> ring
    have hdiff_out : ∀ u, f' v u - fl.f v u =
        if IsPathEdge l v u then min δ (N.cap v u - fl.f v u)
        else if IsPathEdge l u v then -(δ - min δ (N.cap u v - fl.f u v))
        else 0 := by
      intro u; rw [hf'_eq]; split_ifs <;> ring


    simp_rw [hdiff_in, hdiff_out]


    have hcomb : ∀ u, (if IsPathEdge l u v then min δ (N.cap u v - fl.f u v)
        else if IsPathEdge l v u then -(δ - min δ (N.cap v u - fl.f v u)) else (0:ℝ)) -
        (if IsPathEdge l v u then min δ (N.cap v u - fl.f v u)
        else if IsPathEdge l u v then -(δ - min δ (N.cap u v - fl.f u v)) else 0) =
        if IsPathEdge l u v then δ else if IsPathEdge l v u then -δ else 0 := by
      intro u
      by_cases huv : IsPathEdge l u v
      · have hvu : ¬IsPathEdge l v u := fun h => hnodup_disjoint u v ⟨huv, h⟩
        simp [huv, hvu]
      · by_cases hvu : IsPathEdge l v u
        · simp [huv, hvu]
        · simp [huv, hvu]
    suffices h0 : (∑ x : V, ((if IsPathEdge l x v then min δ (N.cap x v - fl.f x v)
        else if IsPathEdge l v x then -(δ - min δ (N.cap v x - fl.f v x)) else 0) -
        (if IsPathEdge l v x then min δ (N.cap v x - fl.f v x)
        else if IsPathEdge l x v then -(δ - min δ (N.cap x v - fl.f x v)) else 0))) = 0 by
      linarith [Finset.sum_sub_distrib (f := fun x => if IsPathEdge l x v then min δ (N.cap x v - fl.f x v) else if IsPathEdge l v x then -(δ - min δ (N.cap v x - fl.f v x)) else 0) (g := fun x => if IsPathEdge l v x then min δ (N.cap v x - fl.f v x) else if IsPathEdge l x v then -(δ - min δ (N.cap x v - fl.f x v)) else 0) (s := Finset.univ)]
    simp_rw [hcomb]


    by_cases hv : v ∈ l
    · obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hv
      have hk_pos : 0 < k := by
        by_contra h; push_neg at h; interval_cases k
        exact hvs (hk_eq.symm.trans hl0)
      have hk_lt_pred : k + 1 < l.length := by
        by_contra h; push_neg at h
        have hk_last : k = l.length - 1 := by omega
        have : l[k]'hk_lt = l[l.length - 1]'(by omega) := by congr 1
        exact hvt (hk_eq.symm.trans (this.trans hln))

      have hin_ex : IsPathEdge l (l[k-1]'(by omega)) v :=
        ⟨⟨k-1, by omega⟩, by simp, by simp [show k - 1 + 1 = k from by omega, hk_eq]⟩
      have hout_ex : IsPathEdge l v (l[k+1]'(by omega)) :=
        ⟨⟨k, by omega⟩, by simp [hk_eq.symm], by simp⟩
      have hin_unique : ∀ u, IsPathEdge l u v → u = l[k-1]'(by omega) := by
        intro u ⟨⟨i, hi⟩, hiu, hiv'⟩
        have hidx : (⟨i + 1, by omega⟩ : Fin l.length) = ⟨k, hk_lt⟩ := by
          apply (hnodup.get_inj_iff).mp
          simp [List.get_eq_getElem, hiv', hk_eq]
        have : i + 1 = k := by simpa using hidx
        have hi_eq : i = k - 1 := by omega
        simp only [List.get_eq_getElem] at hiu
        convert hiu.symm using 1
        congr 1; omega
      have hout_unique : ∀ u, IsPathEdge l v u → u = l[k+1]'(by omega) := by
        intro u ⟨⟨i, hi⟩, hiv', hiu⟩
        have hidx : (⟨i, by omega⟩ : Fin l.length) = ⟨k, hk_lt⟩ := by
          apply (hnodup.get_inj_iff).mp
          simp [List.get_eq_getElem, hiv', hk_eq]
        have : i = k := by simpa using hidx
        simp only [List.get_eq_getElem] at hiu
        convert hiu.symm using 1
        congr 1; omega

      have hne_pred_succ : l[k-1]'(by omega) ≠ l[k+1]'(by omega) := by
        intro heq
        have := (hnodup.getElem_inj_iff (hi := (by omega : k-1 < l.length)) (hj := (by omega : k+1 < l.length))).mp heq
        omega

      have hrewrite : ∀ x : V, (if IsPathEdge l x v then δ else if IsPathEdge l v x then -δ else (0:ℝ)) =
          (if x = l[k-1]'(by omega) then δ else 0) + (if x = l[k+1]'(by omega) then -δ else 0) := by
        intro x
        by_cases hxv : IsPathEdge l x v
        · have hxeq := hin_unique x hxv
          have hvx : ¬IsPathEdge l v x := fun h => hnodup_disjoint x v ⟨hxv, h⟩
          simp only [hxv, hvx, if_true, if_false]
          rw [hxeq, if_pos rfl, if_neg hne_pred_succ]; ring
        · by_cases hvx : IsPathEdge l v x
          · have hxeq := hout_unique x hvx
            have hxne : x ≠ l[k-1]'(by omega) := by
              intro heq; rw [heq] at hvx
              exact hnodup_disjoint (l[k-1]'(by omega)) v ⟨hin_ex, hvx⟩
            simp only [hxv, hvx, if_true, if_false]
            subst hxeq; simp [hne_pred_succ.symm]
          · have hxne1 : x ≠ l[k-1]'(by omega) := fun heq => hxv (heq ▸ hin_ex)
            have hxne2 : x ≠ l[k+1]'(by omega) := fun heq => hvx (heq ▸ hout_ex)
            simp only [hxv, hvx, if_false, if_neg hxne1, if_neg hxne2, add_zero]
      simp_rw [hrewrite, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    ·
      have hno_in : ∀ u, ¬IsPathEdge l u v :=
        fun u ⟨⟨i, hi⟩, _, hiv⟩ => hv (hiv ▸ List.getElem_mem (by omega))
      have hno_out : ∀ u, ¬IsPathEdge l v u :=
        fun u ⟨⟨i, hi⟩, hiv, _⟩ => hv (hiv ▸ List.getElem_mem (by omega))
      apply Finset.sum_eq_zero; intro x _
      simp [hno_in x, hno_out x]

  ·
    unfold flowValue
    suffices hsuff : (∑ v : V, f' N.s v) - (∑ v : V, fl.f N.s v) -
        ((∑ v : V, f' v N.s) - (∑ v : V, fl.f v N.s)) = δ by linarith
    have hlhs : (∑ v : V, f' N.s v) - (∑ v : V, fl.f N.s v) = ∑ v : V, (f' N.s v - fl.f N.s v) := by
      rw [← Finset.sum_sub_distrib]
    have hrhs : (∑ v : V, f' v N.s) - (∑ v : V, fl.f v N.s) = ∑ v : V, (f' v N.s - fl.f v N.s) := by
      rw [← Finset.sum_sub_distrib]
    rw [hlhs, hrhs]

    have hpe_s_in : ∀ u, ¬IsPathEdge l u N.s := by
      intro u ⟨⟨i, hi⟩, _, hiv⟩
      have hidx : (⟨i + 1, by omega⟩ : Fin l.length) = ⟨0, by omega⟩ := by
        apply (hnodup.get_inj_iff).mp
        simp [List.get_eq_getElem, hiv, hl0]
      simpa using hidx
    have hpe_s_out_ex : IsPathEdge l N.s (l[1]'(by omega)) :=
      ⟨⟨0, by omega⟩, by simp [hl0.symm], by simp⟩
    have hpe_s_out_unique : ∀ u, IsPathEdge l N.s u → u = l[1]'(by omega) := by
      intro u ⟨⟨i, hi⟩, his, hiu⟩
      have hidx : (⟨i, by omega⟩ : Fin l.length) = ⟨0, by omega⟩ := by
        apply (hnodup.get_inj_iff).mp
        simp [List.get_eq_getElem, his, hl0]
      have hi0 : i = 0 := by simpa using hidx
      simp only [List.get_eq_getElem] at hiu
      convert hiu.symm using 1; congr 1; omega

    have hdiff_out_s : ∀ u, f' N.s u - fl.f N.s u =
        if IsPathEdge l N.s u then min δ (N.cap N.s u - fl.f N.s u) else 0 := by
      intro u; rw [hf'_eq]; split_ifs with h1 h2
      · ring
      · exact absurd h2 (hpe_s_in u)
      · ring
    have hdiff_in_s : ∀ u, f' u N.s - fl.f u N.s =
        if IsPathEdge l N.s u then -(δ - min δ (N.cap N.s u - fl.f N.s u)) else 0 := by
      intro u; rw [hf'_eq]
      have h_not : ¬IsPathEdge l u N.s := hpe_s_in u
      simp only [h_not, if_false]
      split_ifs with h2
      · ring
      · ring
    simp_rw [hdiff_out_s, hdiff_in_s]

    have hout_sum : (∑ u : V, if IsPathEdge l N.s u then min δ (N.cap N.s u - fl.f N.s u) else (0:ℝ)) =
        min δ (N.cap N.s (l[1]'(by omega)) - fl.f N.s (l[1]'(by omega))) := by
      have := @Finset.sum_eq_single_of_mem V ℝ _ Finset.univ (fun u => if IsPathEdge l N.s u then min δ (N.cap N.s u - fl.f N.s u) else 0) (l[1]'(by omega)) (Finset.mem_univ _)
        (fun u _ hne => if_neg (fun h => absurd (hpe_s_out_unique u h) hne))
      rw [this]; simp only [hpe_s_out_ex, if_true]
    have hin_sum : (∑ u : V, if IsPathEdge l N.s u then -(δ - min δ (N.cap N.s u - fl.f N.s u)) else (0:ℝ)) =
        -(δ - min δ (N.cap N.s (l[1]'(by omega)) - fl.f N.s (l[1]'(by omega)))) := by
      have := @Finset.sum_eq_single_of_mem V ℝ _ Finset.univ (fun u => if IsPathEdge l N.s u then -(δ - min δ (N.cap N.s u - fl.f N.s u)) else 0) (l[1]'(by omega)) (Finset.mem_univ _)
        (fun u _ hne => if_neg (fun h => absurd (hpe_s_out_unique u h) hne))
      rw [this]; simp only [hpe_s_out_ex, if_true]
    rw [hout_sum, hin_sum]; ring

theorem multi_hop_augment
    (N : FlowNetwork V) (fl : STFlow N)
    (htrans : Relation.TransGen (resAdj' N fl) N.s N.t)
    (c : V) (hsc : resAdj' N fl N.s c) (hne : c ≠ N.t)
    (hct : Relation.ReflTransGen (resAdj' N fl) c N.t)
    (d : V) (hsd : Relation.ReflTransGen (resAdj' N fl) N.s d)
    (hdt : resAdj' N fl d N.t) (hds : d ≠ N.s) :
    ∃ fl' : STFlow N, flowValue N fl < flowValue N fl' := by

  have hreach := Relation.TransGen.to_reflTransGen htrans
  obtain ⟨l, hne_l, hchain_l, hnodup_l, hhead_l, hlast_l, hlen_l⟩ :=
    exists_nodup_chain (resAdj' N fl) N.s N.t N.s_ne_t hreach
  exact general_path_augment N fl l hne_l hchain_l hnodup_l hlen_l hhead_l hlast_l

theorem augment_along_residual_path {V : Type*} [Fintype V] [DecidableEq V]
    (N : FlowNetwork V) (fl : STFlow N) (hreach : ResReachable N fl N.t) :
    ∃ fl' : STFlow N, flowValue N fl < flowValue N fl' := by

  have htrans : Relation.TransGen (resAdj' N fl) N.s N.t :=
    (Relation.reflTransGen_iff_eq_or_transGen.mp hreach).resolve_left (Ne.symm N.s_ne_t)

  obtain ⟨c, hsc, hct⟩ := Relation.TransGen.head'_iff.mp htrans


  rcases eq_or_ne c N.t with rfl | hne
  ·

    have hadj := hsc
    unfold resAdj' resCap' at hadj
    by_cases hcase : fl.f N.s N.t < N.cap N.s N.t
    ·
      have hε_pos : (N.cap N.s N.t - fl.f N.s N.t) / 2 > 0 := by linarith
      have hε_le : fl.f N.s N.t + (N.cap N.s N.t - fl.f N.s N.t) / 2 ≤ N.cap N.s N.t := by
        linarith
      set ε := (N.cap N.s N.t - fl.f N.s N.t) / 2
      set f' : V → V → ℝ := fun u v =>
        if u = N.s ∧ v = N.t then fl.f u v + ε else fl.f u v
      have hf'_eq : ∀ u v, f' u v =
          if u = N.s ∧ v = N.t then fl.f u v + ε else fl.f u v :=
        fun u v => rfl
      refine ⟨⟨f', ?_, ?_, ?_⟩, ?_⟩
      ·
        intro u v; rw [hf'_eq]; split_ifs with h
        · linarith [fl.flow_nonneg u v]
        · exact fl.flow_nonneg u v
      ·
        intro u v; rw [hf'_eq]; split_ifs with h
        · obtain ⟨hu, hv⟩ := h; subst hu; subst hv; exact hε_le
        · exact fl.flow_cap u v
      ·
        intro v hvs hvt
        have h1 : (∑ u : V, f' u v) = ∑ u : V, fl.f u v := by
          apply Finset.sum_congr rfl; intro u _; rw [hf'_eq]; simp [hvt]
        have h2 : (∑ u : V, f' v u) = ∑ u : V, fl.f v u := by
          apply Finset.sum_congr rfl; intro u _; rw [hf'_eq]; simp [hvs]
        rw [h1, h2]; exact fl.conservation v hvs hvt
      ·
        unfold flowValue
        have hout : (∑ v : V, f' N.s v) = (∑ v : V, fl.f N.s v) + ε := by
          have : ∀ v, f' N.s v = fl.f N.s v + if v = N.t then ε else 0 := by
            intro v; rw [hf'_eq]; simp; split_ifs <;> ring
          simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq',
            Finset.mem_univ, if_true]
        have hin : (∑ v : V, f' v N.s) = ∑ v : V, fl.f v N.s := by
          apply Finset.sum_congr rfl; intro v _; rw [hf'_eq]; simp [N.s_ne_t]
        linarith
    ·
      push_neg at hcase
      have hfts : fl.f N.t N.s > 0 := by linarith [fl.flow_cap N.s N.t]
      have hε_pos : fl.f N.t N.s / 2 > 0 := by linarith
      have hε_nonneg : fl.f N.t N.s - fl.f N.t N.s / 2 ≥ 0 := by linarith
      have hε_le_cap : fl.f N.t N.s - fl.f N.t N.s / 2 ≤ N.cap N.t N.s := by
        linarith [fl.flow_cap N.t N.s]
      set ε := fl.f N.t N.s / 2
      set f' : V → V → ℝ := fun u v =>
        if u = N.t ∧ v = N.s then fl.f u v - ε else fl.f u v
      have hf'_eq : ∀ u v, f' u v =
          if u = N.t ∧ v = N.s then fl.f u v - ε else fl.f u v :=
        fun u v => rfl
      refine ⟨⟨f', ?_, ?_, ?_⟩, ?_⟩
      ·
        intro u v; rw [hf'_eq]; split_ifs with h
        · obtain ⟨hu, hv⟩ := h; subst hu; subst hv; linarith
        · exact fl.flow_nonneg u v
      ·
        intro u v; rw [hf'_eq]; split_ifs with h
        · obtain ⟨hu, hv⟩ := h; subst hu; subst hv; linarith
        · exact fl.flow_cap u v
      ·
        intro v hvs hvt
        have h1 : (∑ u : V, f' u v) = ∑ u : V, fl.f u v := by
          apply Finset.sum_congr rfl; intro u _; rw [hf'_eq]; simp [hvs]
        have h2 : (∑ u : V, f' v u) = ∑ u : V, fl.f v u := by
          apply Finset.sum_congr rfl; intro u _; rw [hf'_eq]; simp [hvt]
        rw [h1, h2]; exact fl.conservation v hvs hvt
      ·
        unfold flowValue
        have hout : (∑ v : V, f' N.s v) = ∑ v : V, fl.f N.s v := by
          apply Finset.sum_congr rfl; intro v _; rw [hf'_eq]; simp [N.s_ne_t]
        have hin : (∑ v : V, f' v N.s) = (∑ v : V, fl.f v N.s) - ε := by
          have : ∀ v, f' v N.s = fl.f v N.s - if v = N.t then ε else 0 := by
            intro v; rw [hf'_eq]; simp; split_ifs <;> ring
          simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq',
            Finset.mem_univ, if_true]
        linarith
  ·

    obtain ⟨d, hsd, hdt⟩ := Relation.TransGen.tail'_iff.mp htrans


    rcases eq_or_ne d N.s with rfl | hds
    ·

      have hadj := hdt
      unfold resAdj' resCap' at hadj
      by_cases hcase : fl.f N.s N.t < N.cap N.s N.t
      · have hε_pos : (N.cap N.s N.t - fl.f N.s N.t) / 2 > 0 := by linarith
        have hε_le : fl.f N.s N.t + (N.cap N.s N.t - fl.f N.s N.t) / 2 ≤ N.cap N.s N.t := by
          linarith
        set ε := (N.cap N.s N.t - fl.f N.s N.t) / 2
        set f' : V → V → ℝ := fun u v =>
          if u = N.s ∧ v = N.t then fl.f u v + ε else fl.f u v
        have hf'_eq : ∀ u v, f' u v =
            if u = N.s ∧ v = N.t then fl.f u v + ε else fl.f u v :=
          fun u v => rfl
        refine ⟨⟨f', ?_, ?_, ?_⟩, ?_⟩
        · intro u v; rw [hf'_eq]; split_ifs with h
          · linarith [fl.flow_nonneg u v]
          · exact fl.flow_nonneg u v
        · intro u v; rw [hf'_eq]; split_ifs with h
          · obtain ⟨hu, hv⟩ := h; subst hu; subst hv; exact hε_le
          · exact fl.flow_cap u v
        · intro v hvs hvt
          have h1 : (∑ u : V, f' u v) = ∑ u : V, fl.f u v := by
            apply Finset.sum_congr rfl; intro u _; rw [hf'_eq]; simp [hvt]
          have h2 : (∑ u : V, f' v u) = ∑ u : V, fl.f v u := by
            apply Finset.sum_congr rfl; intro u _; rw [hf'_eq]; simp [hvs]
          rw [h1, h2]; exact fl.conservation v hvs hvt
        · unfold flowValue
          have hout : (∑ v : V, f' N.s v) = (∑ v : V, fl.f N.s v) + ε := by
            have : ∀ v, f' N.s v = fl.f N.s v + if v = N.t then ε else 0 := by
              intro v; rw [hf'_eq]; simp; split_ifs <;> ring
            simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq',
              Finset.mem_univ, if_true]
          have hin : (∑ v : V, f' v N.s) = ∑ v : V, fl.f v N.s := by
            apply Finset.sum_congr rfl; intro v _; rw [hf'_eq]; simp [N.s_ne_t]
          linarith
      · push_neg at hcase
        have hfts : fl.f N.t N.s > 0 := by linarith [fl.flow_cap N.s N.t]
        have hε_pos : fl.f N.t N.s / 2 > 0 := by linarith
        have hε_nonneg : fl.f N.t N.s - fl.f N.t N.s / 2 ≥ 0 := by linarith
        set ε := fl.f N.t N.s / 2
        set f' : V → V → ℝ := fun u v =>
          if u = N.t ∧ v = N.s then fl.f u v - ε else fl.f u v
        have hf'_eq : ∀ u v, f' u v =
            if u = N.t ∧ v = N.s then fl.f u v - ε else fl.f u v :=
          fun u v => rfl
        refine ⟨⟨f', ?_, ?_, ?_⟩, ?_⟩
        · intro u v; rw [hf'_eq]; split_ifs with h
          · obtain ⟨hu, hv⟩ := h; subst hu; subst hv; linarith [hε_nonneg]
          · exact fl.flow_nonneg u v
        · intro u v; rw [hf'_eq]; split_ifs with h
          · obtain ⟨hu, hv⟩ := h; subst hu; subst hv; linarith [fl.flow_cap N.t N.s]
          · exact fl.flow_cap u v
        · intro v hvs hvt
          have h1 : (∑ u : V, f' u v) = ∑ u : V, fl.f u v := by
            apply Finset.sum_congr rfl; intro u _; rw [hf'_eq]; simp [hvs]
          have h2 : (∑ u : V, f' v u) = ∑ u : V, fl.f v u := by
            apply Finset.sum_congr rfl; intro u _; rw [hf'_eq]; simp [hvt]
          rw [h1, h2]; exact fl.conservation v hvs hvt
        · unfold flowValue
          have hout : (∑ v : V, f' N.s v) = ∑ v : V, fl.f N.s v := by
            apply Finset.sum_congr rfl; intro v _; rw [hf'_eq]; simp [N.s_ne_t]
          have hin : (∑ v : V, f' v N.s) = (∑ v : V, fl.f v N.s) - ε := by
            have : ∀ v, f' v N.s = fl.f v N.s - if v = N.t then ε else 0 := by
              intro v; rw [hf'_eq]; simp; split_ifs <;> ring
            simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq',
              Finset.mem_univ, if_true]
          linarith
    ·


      exact multi_hop_augment N fl htrans c hsc hne hct d hsd hdt hds

theorem exists_better_flow_of_resReachable (N : FlowNetwork V) (fl : STFlow N)
    (hreach : ResReachable N fl N.t) :
    ∃ fl' : STFlow N, flowValue N fl < flowValue N fl' :=
  augment_along_residual_path N fl hreach

theorem isMaxFlow_iff_noAugmentingPath (N : FlowNetwork V) (fl : STFlow N) :
    IsMaxFlow N fl ↔ NoAugmentingPath N fl := by
  constructor
  ·

    intro hmax hreach
    obtain ⟨fl', hfl'⟩ := exists_better_flow_of_resReachable N fl hreach
    have := hmax fl'
    linarith
  ·
    exact isMaxFlow_of_noAugmentingPath N fl

end NetworkFlow
