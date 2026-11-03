/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLnGapAnalysis
import Mathlib.LinearAlgebra.Dimension.Finite

namespace GLnBuilding


section FinsetGap

variable {n : ℕ}

/-- The cardinality of any `Finset (Fin n)` is at most $n$. -/
lemma finset_card_le_n (S : Finset (Fin n)) : S.card ≤ n := by
  calc S.card ≤ Fintype.card (Fin n) := Finset.card_le_univ S
    _ = n := Fintype.card_fin n

/-- $|U \setminus L| = |U| - |L|$ when $L \subseteq U$. -/
lemma finset_card_sdiff_sub {lower upper : Finset (Fin n)} (hsub : lower ⊆ upper) :
    (upper \ lower).card = upper.card - lower.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]

/-- In a strictly increasing chain of non-empty finsets, the $i$-th term has cardinality
at least $i+1$. -/
lemma chain_card_ge_succ {chain : List (Finset (Fin n))}
    (hpw : chain.Pairwise (· ⊂ ·))
    (hne : ∀ S ∈ chain, S.Nonempty)
    (i : ℕ) (hi : i < chain.length) :
    i + 1 ≤ (chain[i]).card := by
  induction i with
  | zero => exact Finset.card_pos.mpr (hne _ (List.getElem_mem hi))
  | succ k ih =>
    have hk : k < chain.length := by omega
    have := ih hk
    have := Finset.card_lt_card
      (List.pairwise_iff_getElem.mp hpw k (k + 1) hk hi (by omega))
    omega

/-- Core filler: if $|U \setminus L| \ge 2$, pick two distinct elements $a, b$ and form
$L \cup \{a\}$, $L \cup \{b\}$, giving two distinct intermediate proper non-empty finsets. -/
lemma gap_filler_core (lower upper : Finset (Fin n))
    (hsub : lower ⊆ upper) (hcard : 2 ≤ (upper \ lower).card) :
    ∃ T₁ T₂ : Finset (Fin n),
      T₁ ≠ T₂ ∧ T₁.Nonempty ∧ T₁ ≠ Finset.univ ∧
      T₂.Nonempty ∧ T₂ ≠ Finset.univ ∧
      lower ⊂ T₁ ∧ T₁ ⊂ upper ∧ lower ⊂ T₂ ∧ T₂ ⊂ upper := by
  have hpos1 : 0 < (upper \ lower).card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos1
  have hpos2 : 0 < ((upper \ lower).erase a).card := by
    rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, hb_erase⟩ := Finset.card_pos.mp hpos2
  have hb := Finset.mem_of_mem_erase hb_erase
  have hab : a ≠ b := fun heq => by subst heq; simp at hb_erase
  rw [Finset.mem_sdiff] at ha hb
  refine ⟨insert a lower, insert b lower, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h; apply hab
    have hmem := (Finset.ext_iff.mp h a).mp (Finset.mem_insert_self a lower)
    simp [Finset.mem_insert] at hmem
    rcases hmem with rfl | haL
    · rfl
    · exact absurd haL ha.2
  · exact ⟨a, Finset.mem_insert_self a lower⟩
  · intro h; have hci := Finset.card_insert_of_notMem ha.2
    rw [h, Finset.card_univ, Fintype.card_fin] at hci
    have hcle := finset_card_le_n upper
    have hsd := finset_card_sdiff_sub hsub
    omega
  · exact ⟨b, Finset.mem_insert_self b lower⟩
  · intro h; have hci := Finset.card_insert_of_notMem hb.2
    rw [h, Finset.card_univ, Fintype.card_fin] at hci
    have hcle := finset_card_le_n upper
    have hsd := finset_card_sdiff_sub hsub
    omega
  · exact Finset.ssubset_insert ha.2
  ·
    constructor
    · intro x hx; simp [Finset.mem_insert] at hx
      rcases hx with rfl | hx; exact ha.1; exact hsub hx
    · intro h_eq
      have hsub' : upper \ lower ⊆ {a} := by
        intro x hx; rw [Finset.mem_sdiff] at hx; rw [Finset.mem_singleton]
        have hmem := h_eq hx.1; simp [Finset.mem_insert] at hmem
        rcases hmem with rfl | hxL; rfl; exact absurd hxL hx.2
      have := Finset.card_le_card hsub'; simp at this; omega
  · exact Finset.ssubset_insert hb.2
  · constructor
    · intro x hx; simp [Finset.mem_insert] at hx
      rcases hx with rfl | hx; exact hb.1; exact hsub hx
    · intro h_eq
      have hsub' : upper \ lower ⊆ {b} := by
        intro x hx; rw [Finset.mem_sdiff] at hx; rw [Finset.mem_singleton]
        have hmem := h_eq hx.1; simp [Finset.mem_insert] at hmem
        rcases hmem with rfl | hxL; rfl; exact absurd hxL hx.2
      have := Finset.card_le_card hsub'; simp at this; omega

/-- Earlier terms of a strictly-increasing chain are subsets of later terms. -/
lemma chain_elem_subset_of_lt {chain : List (Finset (Fin n))}
    (hpw : chain.Pairwise (· ⊂ ·))
    {bound j : ℕ} (hj : j < chain.length) (hbound : bound < chain.length)
    (hjb : j ≤ bound) :
    chain[j] ⊆ chain[bound] := by
  rcases eq_or_lt_of_le hjb with rfl | hlt
  · exact Finset.Subset.refl _
  · exact (List.pairwise_iff_getElem.mp hpw j bound hj hbound hlt).1

/-- Proof of `FinsetChainGapHyp`: any length-$(n-2)$ chain of proper non-empty subsets of
$\mathrm{Fin}\ n$ contains a position where two distinct insertions fit, by analysing
where cardinalities first deviate from the "tight" pattern $|S_i| = i+1$. -/
noncomputable def finsetChainGapHyp (n : ℕ) (hn2 : 2 ≤ n) : FinsetChainGapHyp n where
  find_gap := fun chain hchain hne hproper hlen => by
    rw [List.isChain_iff_pairwise] at hchain

    by_cases hn : n ≤ 2
    · have hn_eq : n = 2 := by omega
      subst hn_eq
      have hnil : chain.length = 0 := by omega
      have hchain_nil := List.eq_nil_of_length_eq_zero hnil; subst hchain_nil
      refine ⟨{(0 : Fin 2)}, {(1 : Fin 2)}, 0, ?_, Finset.singleton_nonempty _,
              ?_, Finset.singleton_nonempty _, ?_,
              le_refl _, fun S hS => absurd hS (List.not_mem_nil),
              fun S hS => absurd hS (List.not_mem_nil),
              fun S hS => absurd hS (List.not_mem_nil),
              fun S hS => absurd hS (List.not_mem_nil)⟩
      · intro h; have := Finset.ext_iff.mp h (0 : Fin 2); simp at this
      · intro h; have := Finset.ext_iff.mp h (1 : Fin 2); simp at this
      · intro h; have := Finset.ext_iff.mp h (0 : Fin 2); simp at this
    · push_neg at hn
      have hn3 : 3 ≤ n := hn
      have hlen_pos : 0 < chain.length := by omega

      by_cases hall : ∀ i, ∀ hi : i < chain.length, (chain[i]).card = i + 1
      ·
        have hlast : chain.length - 1 < chain.length := by omega
        have hlower_card : (chain[chain.length - 1]).card = n - 2 := by
          rw [hall (chain.length - 1) hlast, hlen]; omega
        have hdiff : 2 ≤ (Finset.univ \ chain[chain.length - 1]).card := by
          rw [finset_card_sdiff_sub (Finset.subset_univ _),
              Finset.card_univ, Fintype.card_fin, hlower_card]; omega
        obtain ⟨T₁, T₂, hne12, hne1, hpr1, hne2, hpr2, hlo1, hhi1, hlo2, hhi2⟩ :=
          gap_filler_core _ _ (Finset.subset_univ _) hdiff
        refine ⟨T₁, T₂, chain.length, hne12, hne1, hpr1, hne2, hpr2, le_refl _,
                ?_, ?_, ?_, ?_⟩
        · intro S hS; rw [List.take_length] at hS
          have hS_lower : S ⊆ chain[chain.length - 1] := by
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
            exact chain_elem_subset_of_lt hchain hj hlast (by omega)
          exact Finset.ssubset_of_subset_of_ssubset hS_lower hlo1
        · intro S hS; rw [List.drop_length] at hS; exact absurd hS (List.not_mem_nil)
        · intro S hS; rw [List.take_length] at hS
          have hS_lower : S ⊆ chain[chain.length - 1] := by
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
            exact chain_elem_subset_of_lt hchain hj hlast (by omega)
          exact Finset.ssubset_of_subset_of_ssubset hS_lower hlo2
        · intro S hS; rw [List.drop_length] at hS; exact absurd hS (List.not_mem_nil)
      ·
        push_neg at hall
        obtain ⟨i, hi, hmis⟩ := hall

        classical
        let P := fun k => ∃ hk : k < chain.length, (chain[k]'hk).card ≠ k + 1
        have hP : ∃ k, P k := ⟨i, hi, hmis⟩
        let pos := Nat.find hP
        have hpos_spec : P pos := Nat.find_spec hP
        obtain ⟨hpos_lt, hpos_mis⟩ := hpos_spec
        have hpos_card : pos + 2 ≤ (chain[pos]'hpos_lt).card := by
          have := chain_card_ge_succ hchain hne pos hpos_lt; omega
        have hprev : ∀ j, j < pos → (hj : j < chain.length) → (chain[j]'hj).card = j + 1 := by
          intro j hj hjlen
          by_contra h; exact Nat.find_min hP hj ⟨hjlen, h⟩
        by_cases hpos0 : pos = 0
        ·
          have hpos_lt0 : 0 < chain.length := by omega
          have helem_eq : chain[0]'hpos_lt0 = chain[pos]'hpos_lt := by
            congr 1; omega
          have hpos_card0 : 2 ≤ (chain[0]'hpos_lt0).card := by
            rw [helem_eq]; omega
          have hdiff : 2 ≤ (chain[0]'hpos_lt0 \ ∅).card := by simp; omega
          obtain ⟨T₁, T₂, hne12, hne1, hpr1, hne2, hpr2, hlo1, hhi1, hlo2, hhi2⟩ :=
            gap_filler_core ∅ (chain[0]'hpos_lt0) (Finset.empty_subset _) hdiff
          have hupper_proper := hproper _ (List.getElem_mem hpos_lt0)
          refine ⟨T₁, T₂, 0, hne12, hne1, ?_, hne2, ?_, (by omega : 0 ≤ chain.length),
                  fun S hS => absurd hS (by simp), ?_,
                  fun S hS => absurd hS (by simp), ?_⟩
          · intro h; rw [h] at hhi1
            exact absurd (Finset.eq_univ_iff_forall.mpr (fun x => hhi1.1 (Finset.mem_univ x))) hupper_proper
          · intro h; rw [h] at hhi2
            exact absurd (Finset.eq_univ_iff_forall.mpr (fun x => hhi2.1 (Finset.mem_univ x))) hupper_proper
          · intro S hS; rw [List.drop_zero] at hS
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
            by_cases hj0 : j = 0
            · subst hj0; exact hhi1
            · exact Finset.ssubset_of_ssubset_of_subset hhi1
                (List.pairwise_iff_getElem.mp hchain 0 j (by omega) hj (by omega)).1
          · intro S hS; rw [List.drop_zero] at hS
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
            by_cases hj0 : j = 0
            · subst hj0; exact hhi2
            · exact Finset.ssubset_of_ssubset_of_subset hhi2
                (List.pairwise_iff_getElem.mp hchain 0 j (by omega) hj (by omega)).1
        ·
          have hpos_pos : 0 < pos := Nat.pos_of_ne_zero hpos0
          have hprev_idx : pos - 1 < chain.length := by omega
          have hlower_card : (chain[pos - 1]'hprev_idx).card = pos := by
            rw [hprev (pos - 1) (by omega) hprev_idx]; omega
          have hlower_upper : chain[pos - 1]'hprev_idx ⊂ chain[pos]'hpos_lt :=
            List.pairwise_iff_getElem.mp hchain (pos - 1) pos hprev_idx hpos_lt (by omega)
          have hdiff : 2 ≤ (chain[pos]'hpos_lt \ chain[pos - 1]'hprev_idx).card := by
            rw [finset_card_sdiff_sub hlower_upper.1, hlower_card]; omega
          obtain ⟨T₁, T₂, hne12, hne1, hpr1, hne2, hpr2, hlo1, hhi1, hlo2, hhi2⟩ :=
            gap_filler_core _ _ hlower_upper.1 hdiff
          have hupper_proper := hproper _ (List.getElem_mem hpos_lt)
          refine ⟨T₁, T₂, pos, hne12, hne1, ?_, hne2, ?_, (by omega : pos ≤ chain.length),
                  ?_, ?_, ?_, ?_⟩
          · intro h; rw [h] at hhi1
            exact absurd (Finset.eq_univ_iff_forall.mpr (fun x => hhi1.1 (Finset.mem_univ x))) hupper_proper
          · intro h; rw [h] at hhi2
            exact absurd (Finset.eq_univ_iff_forall.mpr (fun x => hhi2.1 (Finset.mem_univ x))) hupper_proper
          · intro S hS
            have hS_lower : S ⊆ chain[pos - 1]'hprev_idx := by
              obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
              have hj_len : j < chain.length := by rw [List.length_take] at hj; omega
              have hj_pos : j ≤ pos - 1 := by rw [List.length_take] at hj; omega
              rw [← List.getElem_take' hj_len (by omega : j < pos)]
              exact chain_elem_subset_of_lt hchain hj_len hprev_idx hj_pos
            exact Finset.ssubset_of_subset_of_ssubset hS_lower hlo1
          · intro S hS
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
            rw [List.length_drop] at hj
            rw [List.getElem_drop]
            by_cases hjp : j = 0
            · subst hjp; simp; exact hhi1
            · exact Finset.ssubset_of_ssubset_of_subset hhi1
                (List.pairwise_iff_getElem.mp hchain pos (pos + j) hpos_lt (by omega) (by omega)).1
          · intro S hS
            have hS_lower : S ⊆ chain[pos - 1]'hprev_idx := by
              obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
              have hj_len : j < chain.length := by rw [List.length_take] at hj; omega
              have hj_pos : j ≤ pos - 1 := by rw [List.length_take] at hj; omega
              rw [← List.getElem_take' hj_len (by omega : j < pos)]
              exact chain_elem_subset_of_lt hchain hj_len hprev_idx hj_pos
            exact Finset.ssubset_of_subset_of_ssubset hS_lower hlo2
          · intro S hS
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
            rw [List.length_drop] at hj
            rw [List.getElem_drop]
            by_cases hjp : j = 0
            · subst hjp; simp; exact hhi2
            · exact Finset.ssubset_of_ssubset_of_subset hhi2
                (List.pairwise_iff_getElem.mp hchain pos (pos + j) hpos_lt (by omega) (by omega)).1

end FinsetGap


section FrameCorrespondence

variable (k : Type*) [Field k] (n : ℕ)

open Classical in
/-- Extract the index set $S \subseteq \mathrm{Fin}\ n$ such that $V = \bigoplus_{i \in S} F.\mathrm{lines}\ i$
(via classical choice), or `∅` if no such $S$ exists. -/
noncomputable def extractFinset (F : Frame k n) (V : Submodule k (Vec k n)) : Finset (Fin n) :=
  if h : F.IsCompatible k n V then Classical.choose h else ∅

/-- For an $F$-compatible $V$, the extracted finset $S$ satisfies $V = \bigoplus_{i \in S} F.\mathrm{lines}\ i$. -/
lemma extractFinset_spec (F : Frame k n) (V : Submodule k (Vec k n))
    (hcompat : F.IsCompatible k n V) :
    V = ⨆ i ∈ extractFinset k n F V, F.lines i := by
  simp only [extractFinset, dif_pos hcompat]
  exact Classical.choose_spec hcompat

/-- $\bigoplus_{i \in S_1} L_i \le \bigoplus_{i \in S_2} L_i$ when $S_1 \subseteq S_2$. -/
lemma biSup_subset_le (F : Frame k n) (S₁ S₂ : Finset (Fin n)) (h : S₁ ⊆ S₂) :
    (⨆ i ∈ S₁, F.lines i) ≤ (⨆ i ∈ S₂, F.lines i) := by
  apply iSup_le_iSup_of_subset
  intro i hi
  exact h hi

/-- If $j \notin S_1$, then $F.\mathrm{lines}\ j$ is not contained in $\bigoplus_{i \in S_1} L_i$,
by the frame's independence. -/
lemma frame_line_not_le_biSup (F : Frame k n) (S₁ : Finset (Fin n))
    {j : Fin n} (hj : j ∉ S₁) :
    ¬(F.lines j ≤ ⨆ i ∈ S₁, F.lines i) := by
  intro hle
  have hindep := F.indep
  have hdisj := hindep.disjoint_biSup (Finset.mem_coe.not.mpr hj)
  have hbot : F.lines j = ⊥ := hdisj.eq_bot_of_le hle
  have h1 := F.one_dim j
  rw [hbot, finrank_bot] at h1
  omega

/-- Strict subset $S_1 \subsetneq S_2$ lifts to strict containment of frame-spans. -/
lemma frame_biSup_ssubset (F : Frame k n) {S₁ S₂ : Finset (Fin n)} (h : S₁ ⊂ S₂) :
    (⨆ i ∈ S₁, F.lines i) < (⨆ i ∈ S₂, F.lines i) := by
  apply lt_of_le_of_ne
  · exact biSup_subset_le k n F S₁ S₂ h.1
  · intro heq
    obtain ⟨j, hj2, hj1⟩ := Finset.exists_of_ssubset h
    have : F.lines j ≤ ⨆ i ∈ S₂, F.lines i :=
      le_iSup₂_of_le j hj2 (le_refl _)
    rw [← heq] at this
    exact frame_line_not_le_biSup k n F S₁ hj1 this

/-- A non-empty index set $S$ produces a non-zero frame-span. -/
lemma frame_biSup_ne_bot (F : Frame k n) {S : Finset (Fin n)} (hne : S.Nonempty) :
    (⨆ i ∈ S, F.lines i) ≠ ⊥ := by
  obtain ⟨j, hj⟩ := hne
  intro h
  have : F.lines j ≤ ⨆ i ∈ S, F.lines i :=
    le_iSup₂_of_le j hj (le_refl _)
  rw [h] at this
  have hbot : F.lines j = ⊥ := le_bot_iff.mp this
  have := F.one_dim j; rw [hbot, finrank_bot] at this; omega

/-- A proper index set $S \ne \mathrm{Finset.univ}$ produces a proper frame-span. -/
lemma frame_biSup_ne_top (F : Frame k n) {S : Finset (Fin n)} (hne : S ≠ Finset.univ) :
    (⨆ i ∈ S, F.lines i) ≠ ⊤ := by
  intro h
  obtain ⟨j, _, hj⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  have : F.lines j ≤ ⨆ i ∈ S, F.lines i := by
    rw [h]; exact le_top
  exact frame_line_not_le_biSup k n F S hj this

/-- Distinct index sets produce distinct frame-spans (injectivity of $S \mapsto \bigoplus_{i \in S} L_i$). -/
lemma frame_biSup_injective (F : Frame k n) {S₁ S₂ : Finset (Fin n)} (hne : S₁ ≠ S₂) :
    (⨆ i ∈ S₁, F.lines i) ≠ (⨆ i ∈ S₂, F.lines i) := by
  intro heq

  have : (∃ a, a ∈ S₁ ∧ a ∉ S₂) ∨ (∃ a, a ∈ S₂ ∧ a ∉ S₁) := by
    by_contra hh
    push_neg at hh
    exact hne (Finset.ext (fun x => ⟨fun h1 => hh.1 x h1, fun h2 => hh.2 x h2⟩))
  rcases this with ⟨j, hj1, hj2⟩ | ⟨j, hj2, hj1⟩
  · have : F.lines j ≤ ⨆ i ∈ S₁, F.lines i :=
      le_iSup₂_of_le j hj1 (le_refl _)
    rw [heq] at this
    exact frame_line_not_le_biSup k n F S₂ hj2 this
  · have : F.lines j ≤ ⨆ i ∈ S₂, F.lines i :=
      le_iSup₂_of_le j hj2 (le_refl _)
    rw [← heq] at this
    exact frame_line_not_le_biSup k n F S₁ hj1 this

/-- Proof of `FrameFinsetCorrespondenceHyp`: bundle the bijection between $F$-compatible
subspaces and subsets of $\mathrm{Fin}\ n$ via `extractFinset` and $S \mapsto \bigoplus_{i \in S} L_i$. -/
noncomputable def frameFinsetCorrespondenceHyp : FrameFinsetCorrespondenceHyp k n where
  extract := extractFinset k n
  extract_eq := fun F V hcompat => extractFinset_spec k n F V hcompat
  extract_ssubset := fun F V₁ V₂ hcompat₁ hcompat₂ hlt => by
    have heq₁ := extractFinset_spec k n F V₁ hcompat₁
    have heq₂ := extractFinset_spec k n F V₂ hcompat₂
    set S₁ := extractFinset k n F V₁
    set S₂ := extractFinset k n F V₂
    by_contra h

    by_cases hsub : S₁ ⊆ S₂
    ·
      have heqs : S₁ = S₂ := by
        rw [Finset.ssubset_iff_subset_ne] at h; push_neg at h
        exact h hsub
      rw [heq₁, heq₂, heqs] at hlt
      exact lt_irrefl _ hlt
    ·
      obtain ⟨j, hj1, hj2⟩ := Finset.not_subset.mp hsub
      have hle : F.lines j ≤ ⨆ i ∈ S₂, F.lines i := by
        calc F.lines j ≤ ⨆ i ∈ S₁, F.lines i :=
              le_iSup₂_of_le j hj1 (le_refl _)
          _ = V₁ := heq₁.symm
          _ ≤ V₂ := hlt.le
          _ = ⨆ i ∈ S₂, F.lines i := heq₂
      exact frame_line_not_le_biSup k n F S₂ hj2 hle
  extract_nonempty := fun F V hcompat hbot => by
    rw [extractFinset_spec k n F V hcompat] at hbot
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hbot
    simp at hbot
  extract_proper := fun F V hcompat htop => by
    rw [extractFinset_spec k n F V hcompat] at htop
    intro h; apply htop
    rw [h]
    simp [F.spanning]
  lift_ssubset := fun F S₁ S₂ h => frame_biSup_ssubset k n F h
  lift_nonempty := fun F S hne => frame_biSup_ne_bot k n F hne
  lift_proper := fun F S hpr => frame_biSup_ne_top k n F hpr
  lift_ne := fun F S₁ S₂ hne => frame_biSup_injective k n F hne

end FrameCorrespondence

end GLnBuilding
