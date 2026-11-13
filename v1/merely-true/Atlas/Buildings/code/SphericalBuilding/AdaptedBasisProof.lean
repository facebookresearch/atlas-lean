/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.BasisExtensionChain
import Atlas.Buildings.code.SphericalBuilding.AdaptedBasisSingle
import Atlas.Buildings.code.SphericalBuilding.BasisFromFlagProof
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.CompleteLattice.Finset

namespace GLnBuilding

open Submodule Module

variable {k : Type*} [Field k]


/-- Hypothesis: any two chambers $\sigma, \tau$ admit a common adapted frame $F$ — i.e.\ a
frame compatible with every subspace appearing in either chamber's chain. -/
structure TwoChamberFrameHyp (k : Type*) [Field k] (n : ℕ) where
  frame_of_two_chambers : ∀ (σ τ : SubspaceFlag k n),
    IsChamber k n σ →
    IsChamber k n τ →
    ∃ F : Frame k n, (∀ V ∈ σ.chain, F.IsCompatible k n V) ∧
                      (∀ V ∈ τ.chain, F.IsCompatible k n V)


section FlagCompletion

/-- Between two subspaces $V < W$ with a dimension gap of at least $2$, there is a strictly
intermediate subspace $U$ with $V < U < W$ and $\dim U = \dim V + 1$. -/
lemma intermediate_submodule {M : Type*} [AddCommGroup M] [Module k M]
    [FiniteDimensional k M]
    {V W : Submodule k M}
    (hVW : V < W)
    (hgap : finrank k V + 2 ≤ finrank k W) :
    ∃ U : Submodule k M, V < U ∧ U < W ∧ finrank k U = finrank k V + 1 := by
  obtain ⟨v, hvW, hvV⟩ := SetLike.exists_of_lt hVW
  have hv_ne : v ≠ 0 := fun h0 => hvV (h0 ▸ V.zero_mem)
  have hdisjoint : Disjoint V (k ∙ v) := by
    rw [disjoint_span_singleton]; intro hmem; exact absurd hmem hvV
  have hdim : finrank k ↥(V ⊔ k ∙ v) = finrank k ↥V + 1 := by
    have := finrank_sup_add_finrank_inf_eq V (k ∙ v)
    rw [hdisjoint.eq_bot, finrank_bot k M, finrank_span_singleton hv_ne] at this
    omega
  refine ⟨V ⊔ k ∙ v, lt_sup_iff_notMem.mpr hvV, ?_, hdim⟩
  apply lt_of_le_of_ne
  · exact sup_le (le_of_lt hVW) (span_le.mpr (Set.singleton_subset_iff.mpr hvW))
  · intro h; rw [h] at hdim; omega

/-- `List.insertIdx` decomposed as `take ++ a :: drop`. -/
lemma insertIdx_eq_take_drop {α : Type*} (l : List α) (i : ℕ) (a : α)
    (hi : i ≤ l.length) :
    l.insertIdx i a = l.take i ++ a :: l.drop i := by
  induction l generalizing i with
  | nil => simp at hi; subst hi; simp [List.insertIdx]
  | cons x xs ih =>
    cases i with
    | zero => simp [List.insertIdx]
    | succ j =>
      have hj : j ≤ xs.length := by simp at hi; exact hi
      simp only [List.insertIdx, List.take, List.drop, List.cons_append]
      show x :: xs.insertIdx j a = x :: (List.take j xs ++ a :: List.drop j xs)
      rw [ih j hj]

/-- `List.insertIdx` preserves `Pairwise R` given the appropriate relations to elements
before and after the insertion point. -/
lemma pairwise_insertIdx {α : Type*} {R : α → α → Prop}
    {l : List α} {a : α} {i : ℕ} (hi : i ≤ l.length)
    (hpw : l.Pairwise R)
    (hleft : ∀ x ∈ l.take i, R x a)
    (hright : ∀ x ∈ l.drop i, R a x) :
    (l.insertIdx i a).Pairwise R := by
  rw [insertIdx_eq_take_drop l i a hi, List.pairwise_append]
  have key : (l.take i ++ l.drop i).Pairwise R := by rw [List.take_append_drop]; exact hpw
  refine ⟨hpw.sublist (List.take_sublist i l),
          List.Pairwise.cons hright (hpw.sublist (List.drop_sublist i l)), ?_⟩
  intro x hx y hy
  cases hy with
  | head _ => exact hleft x hx
  | tail _ hyt => exact (List.pairwise_append.mp key).2.2 x hx y hyt

/-- In a pairwise strictly-increasing non-empty list, every element is $\le$ the last. -/
lemma le_getLast_of_mem_pairwise {α : Type*} [Preorder α]
    {l : List α} (hpw : l.Pairwise (· < ·)) (hne : l ≠ [])
    {a : α} (ha : a ∈ l) : a ≤ l.getLast hne := by
  rw [List.mem_iff_getElem] at ha
  obtain ⟨j, hj, rfl⟩ := ha
  by_cases h : j = l.length - 1
  · have : l[j] = l.getLast hne := by rw [List.getLast_eq_getElem]; congr
    rw [this]
  · have hjlt : j < l.length - 1 := by omega
    have := List.pairwise_iff_getElem.mp hpw j (l.length - 1) hj (by omega) (by omega)
    rw [show l[l.length - 1] = l.getLast hne from by rw [List.getLast_eq_getElem]] at this
    exact le_of_lt this

/-- In a pairwise strictly-increasing non-empty list, the head is $\le$ every element. -/
lemma head_le_of_mem_pairwise {α : Type*} [Preorder α]
    {l : List α} (hpw : l.Pairwise (· < ·)) (hne : l ≠ [])
    {a : α} (ha : a ∈ l) : l.head hne ≤ a := by
  rw [List.mem_iff_getElem] at ha
  obtain ⟨j, hj, rfl⟩ := ha
  by_cases h : j = 0
  · rw [show l[j] = l.head hne from by
      cases l with | nil => exact absurd rfl hne | cons x xs => simp [h]]
  · have : 0 < j := by omega
    have hlt := List.pairwise_iff_getElem.mp hpw 0 j (by
      exact List.ne_nil_iff_length_pos.mp hne) hj this
    rw [show l[0] = l.head hne from by
      cases l with | nil => exact absurd rfl hne | cons x xs => rfl] at hlt
    exact le_of_lt hlt

/-- Any non-empty strict chain of proper subspaces of length $< n-1$ can be extended by one
proper subspace, either at the front, back, or in the middle, while staying a proper chain. -/
lemma extend_flag_chain (n : ℕ)
    (chain : List (Submodule k (Vec k n)))
    (hne : chain ≠ [])
    (hchain : chain.IsChain (· < ·))
    (hproper : ∀ V ∈ chain, V ≠ ⊥ ∧ V ≠ ⊤)
    (hshort : chain.length < n - 1) :
    ∃ (chain' : List (Submodule k (Vec k n))),
      chain'.length = chain.length + 1 ∧
      chain'.IsChain (· < ·) ∧
      (∀ V ∈ chain', V ≠ ⊥ ∧ V ≠ ⊤) ∧
      chain'.length ≤ n - 1 ∧
      (∀ V ∈ chain, V ∈ chain') := by
  classical
  have hn : n ≥ 2 := by
    have : chain.length ≥ 1 := List.ne_nil_iff_length_pos.mp hne
    omega
  have hpw := List.isChain_iff_pairwise.mp hchain
  have hhead := List.head_mem hne
  have hlast := List.getLast_mem hne

  have hfirst_pos : finrank k (chain.head hne) ≥ 1 := by
    have hne_bot := (hproper _ hhead).1
    by_contra h; push_neg at h
    exact hne_bot (finrank_eq_zero.mp (by omega))

  have hlast_bound : finrank k (chain.getLast hne) ≤ n - 1 := by
    have htop := (hproper _ hlast).2
    by_contra h; push_neg at h
    have hle : finrank k (Vec k n) ≤ finrank k (chain.getLast hne) := by
      rw [Module.finrank_fin_fun]; omega
    exact htop (Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hle))

  by_cases hback : finrank k (chain.getLast hne) + 2 ≤ n
  · obtain ⟨U, hU_gt, hU_lt, _⟩ := intermediate_submodule
      (lt_top_iff_ne_top.mpr (hproper _ hlast).2)
      (by rw [finrank_top, Module.finrank_fin_fun]; exact hback)
    refine ⟨chain ++ [U], ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · rw [List.isChain_iff_pairwise, List.pairwise_append]
      exact ⟨hpw, List.pairwise_singleton _ _, fun a ha b hb => by
        simp at hb; subst hb
        exact lt_of_le_of_lt (le_getLast_of_mem_pairwise hpw hne ha) hU_gt⟩
    · intro V hV; rw [List.mem_append] at hV
      cases hV with
      | inl h => exact hproper V h
      | inr h => simp at h; subst h; exact ⟨ne_bot_of_gt hU_gt, ne_top_of_lt hU_lt⟩
    · simp; omega
    · intro V hV; exact List.mem_append.mpr (Or.inl hV)
  · push_neg at hback
    have hlast_eq : finrank k (chain.getLast hne) = n - 1 := by omega

    by_cases hfront : 2 ≤ finrank k (chain.head hne)
    · obtain ⟨U, hU_gt, hU_lt, _⟩ := intermediate_submodule
        (bot_lt_iff_ne_bot.mpr (hproper _ hhead).1)
        (by rw [finrank_bot k (Vec k n)]; omega)
      refine ⟨U :: chain, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · rw [List.isChain_iff_pairwise]
        exact List.Pairwise.cons
          (fun y hy => lt_of_lt_of_le hU_lt (head_le_of_mem_pairwise hpw hne hy)) hpw
      · intro V hV
        cases hV with
        | head => exact ⟨ne_bot_of_gt hU_gt, ne_top_of_lt hU_lt⟩
        | tail _ h => exact hproper V h
      · simp; omega
      · intro V hV; exact List.mem_cons_of_mem _ hV
    · push_neg at hfront
      have hhead_eq : finrank k (chain.head hne) = 1 := by omega

      have hlen_ge2 : chain.length ≥ 2 := by
        by_contra h; push_neg at h
        have hlen1 : chain.length = 1 := by
          have := List.ne_nil_iff_length_pos.mp hne; omega
        have : chain.head hne = chain.getLast hne := by
          cases chain with
          | nil => exact absurd rfl hne
          | cons a l =>
            simp at hlen1
            have : l = [] := hlen1
            subst this; rfl
        rw [this] at hhead_eq; rw [hhead_eq] at hlast_eq; omega

      have hexists_gap : ∃ (i : ℕ) (hi : i + 1 < chain.length),
          finrank k chain[i] + 2 ≤ finrank k chain[i + 1] := by
        by_contra hall; push_neg at hall
        have hgap_one : ∀ (i : ℕ) (hi : i + 1 < chain.length),
            finrank k chain[i + 1] = finrank k chain[i] + 1 := by
          intro i hi
          have hlt := List.pairwise_iff_getElem.mp hpw i (i + 1) (by omega) hi (by omega)
          have := Submodule.finrank_lt_finrank_of_lt hlt
          have := hall i hi; omega
        have hfinrank_eq : ∀ (i : ℕ) (hi : i < chain.length),
            finrank k chain[i] = 1 + i := by
          intro i hi; induction i with
          | zero =>
            have : chain[0] = chain.head hne := by
              cases chain with | nil => exact absurd rfl hne | cons a l => rfl
            rw [this, hhead_eq]
          | succ j ih => rw [hgap_one j (by omega), ih (by omega)]; ring
        have := hfinrank_eq (chain.length - 1) (by omega)
        have hlast_get : chain.getLast hne = chain[chain.length - 1] := by
          rw [List.getLast_eq_getElem]
        rw [hlast_get] at hlast_eq; rw [this] at hlast_eq; omega
      obtain ⟨i, hi, hgap⟩ := hexists_gap
      have hVi_lt : chain[i] < chain[i + 1] :=
        List.pairwise_iff_getElem.mp hpw i (i + 1) (by omega) hi (by omega)
      obtain ⟨U, hU_gt, hU_lt, _⟩ := intermediate_submodule hVi_lt hgap

      refine ⟨chain.insertIdx (i + 1) U, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.length_insertIdx]; simp [show i + 1 ≤ chain.length from by omega]
      · rw [List.isChain_iff_pairwise]
        apply pairwise_insertIdx (show i + 1 ≤ chain.length from by omega) hpw
        ·
          intro x hx
          have hx_mem := List.mem_of_mem_take hx
          rw [List.mem_iff_getElem] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          have hj_bound : j < i + 1 := by
            have := List.length_take_le (i + 1) chain; omega
          have heq : (List.take (i + 1) chain)[j] = chain[j]'(by omega) :=
            List.getElem_take ..
          rw [heq]
          by_cases hji : j = i
          · subst hji; exact hU_gt
          · have hjlt : j < i := by omega
            exact lt_trans (List.pairwise_iff_getElem.mp hpw j i (by omega) (by omega) hjlt) hU_gt
        ·
          intro x hx
          rw [List.mem_iff_getElem] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          have hj_len : i + 1 + j < chain.length := by
            have := @List.length_drop _ (i + 1) chain; omega
          have heq : (List.drop (i + 1) chain)[j] = chain[i + 1 + j]'hj_len :=
            (List.getElem_drop' hj_len).symm
          rw [heq]
          by_cases hj0 : j = 0
          · subst hj0; simp; exact hU_lt
          · exact lt_trans hU_lt
              (List.pairwise_iff_getElem.mp hpw (i + 1) (i + 1 + j) hi hj_len (by omega))
      · intro V hV
        rw [List.mem_insertIdx (by omega)] at hV
        cases hV with
        | inl h => subst h; exact ⟨ne_bot_of_gt hU_gt, ne_top_of_lt hU_lt⟩
        | inr h => exact hproper V h
      · rw [List.length_insertIdx]; simp [show i + 1 ≤ chain.length from by omega]; omega
      · intro V hV
        exact (List.mem_insertIdx (by omega)).mpr (Or.inr hV)

/-- Any non-empty chain of proper subspaces in $k^n$ ($n \ge 2$) can be completed to a
maximal flag of length exactly $n-1$ containing the original chain. -/
lemma flag_completion (n : ℕ) (hn : n ≥ 2)
    (chain : List (Submodule k (Vec k n)))
    (hne : chain ≠ [])
    (hchain : chain.IsChain (· < ·))
    (hproper : ∀ V ∈ chain, V ≠ ⊥ ∧ V ≠ ⊤) :
    ∃ (chain' : List (Submodule k (Vec k n))),
      chain'.length = n - 1 ∧
      chain'.IsChain (· < ·) ∧
      (∀ V ∈ chain', V ≠ ⊥ ∧ V ≠ ⊤) ∧
      (∀ V ∈ chain, V ∈ chain') := by

  have hlen_bound : chain.length ≤ n - 1 := by
    by_contra h; push_neg at h
    have hpw := List.isChain_iff_pairwise.mp hchain
    have : ∀ (i : ℕ) (hi : i < chain.length), finrank k chain[i] ≥ i + 1 := by
      intro i hi; induction i with
      | zero =>
        have : chain[0] = chain.head hne := by
          cases chain with | nil => exact absurd rfl hne | cons a l => rfl
        rw [this]
        have hne_bot := (hproper _ (List.head_mem hne)).1
        by_contra hc; push_neg at hc
        exact hne_bot (finrank_eq_zero.mp (by omega))
      | succ j ih =>
        have := ih (by omega)
        have hlt := List.pairwise_iff_getElem.mp hpw j (j + 1) (by omega) hi (by omega)
        have := Submodule.finrank_lt_finrank_of_lt hlt; omega
    have := this (n - 1) (by omega)
    have hmem : chain[n - 1] ∈ chain := List.getElem_mem (by omega)
    have htop := (hproper _ hmem).2
    have hle : finrank k (Vec k n) ≤ finrank k chain[n - 1] := by
      rw [Module.finrank_fin_fun]; omega
    exact htop (Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hle))

  obtain ⟨deficit, hdeficit⟩ : ∃ d, chain.length + d = n - 1 := ⟨n - 1 - chain.length, by omega⟩
  induction deficit generalizing chain with
  | zero =>
    exact ⟨chain, by omega, hchain, hproper, fun V hV => hV⟩
  | succ d ih =>
    have hshort : chain.length < n - 1 := by omega
    obtain ⟨chain', hlen', hchain', hproper', _, hcontains'⟩ :=
      extend_flag_chain n chain hne hchain hproper hshort
    have hne' : chain' ≠ [] := by intro h; simp [h] at hlen'
    obtain ⟨chain'', hlen'', hchain'', hproper'', hcontains''⟩ :=
      ih chain' hne' hchain' hproper' (by omega) (by omega)
    exact ⟨chain'', hlen'', hchain'', hproper'',
      fun V hV => hcontains'' V (hcontains' V hV)⟩

end FlagCompletion


/-- Combine the two-chamber frame hypothesis with flag completion to deduce the
common-apartment property: any two flags $\sigma, \tau$ lie in a common apartment, by first
completing each to a chamber and then applying `TwoChamberFrameHyp`. -/
noncomputable def commonApartmentFromHyps (n : ℕ) (hn : n ≥ 2)
    (h : TwoChamberFrameHyp k n) : CommonApartmentHyp k n where
  refine_flags := fun σ τ => by

    obtain ⟨σ_chain, hσ_len, hσ_chain, hσ_proper, hσ_contains⟩ :=
      flag_completion n hn σ.chain σ.chain_nonempty
        σ.chain_strictly_increasing σ.chain_proper
    let σ' : SubspaceFlag k n :=
      { chain := σ_chain
        chain_nonempty := by intro h; simp [h] at hσ_len; omega
        chain_strictly_increasing := hσ_chain
        chain_proper := hσ_proper }
    have hσ_chamber : IsChamber k n σ' := hσ_len

    obtain ⟨τ_chain, hτ_len, hτ_chain, hτ_proper, hτ_contains⟩ :=
      flag_completion n hn τ.chain τ.chain_nonempty
        τ.chain_strictly_increasing τ.chain_proper
    let τ' : SubspaceFlag k n :=
      { chain := τ_chain
        chain_nonempty := by intro h; simp [h] at hτ_len; omega
        chain_strictly_increasing := hτ_chain
        chain_proper := hτ_proper }
    have hτ_chamber : IsChamber k n τ' := hτ_len

    obtain ⟨F, hF_σ, hF_τ⟩ := h.frame_of_two_chambers σ' τ' hσ_chamber hτ_chamber
    exact ⟨F, fun V hV => hF_σ V (hσ_contains V hV),
               fun V hV => hF_τ V (hτ_contains V hV)⟩

end GLnBuilding
