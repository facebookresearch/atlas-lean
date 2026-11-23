/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLnPanelExtension

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- `List.insertIdx` decomposed as `take ++ a :: drop`. -/
lemma insertIdx_eq_take_append_drop' {α : Type*} {l : List α} {w : α} {i : ℕ}
    (hi : i ≤ l.length) :
    l.insertIdx i w = l.take i ++ w :: l.drop i := by
  induction l generalizing i with
  | nil => simp at hi; subst hi; simp [List.insertIdx]
  | cons a t ih =>
    cases i with
    | zero => simp [List.insertIdx]
    | succ j =>
      simp only [List.insertIdx, List.take, List.drop, List.cons_append]
      exact congrArg (List.cons a) (ih (by simp at hi; omega))

/-- Inserting an element at index $i$ preserves `Pairwise R`, given the appropriate relation
to elements before and after position $i$. -/
lemma pairwise_insertIdx_of_pairwise {α : Type*} {R : α → α → Prop}
    {l : List α} {w : α} {i : ℕ}
    (hpw : l.Pairwise R)
    (hi : i ≤ l.length)
    (hbefore : ∀ x ∈ l.take i, R x w)
    (hafter : ∀ y ∈ l.drop i, R w y) :
    (l.insertIdx i w).Pairwise R := by
  rw [insertIdx_eq_take_append_drop' hi]
  show (l.take i ++ ([w] ++ l.drop i)).Pairwise R
  have hpw' : (l.take i ++ l.drop i).Pairwise R := by
    rw [List.take_append_drop]; exact hpw
  rw [← List.append_assoc]
  rw [List.pairwise_append] at hpw' ⊢
  obtain ⟨hpw1, hpw2, hpw12⟩ := hpw'
  refine ⟨?_, hpw2, ?_⟩
  · rw [List.pairwise_append]
    exact ⟨hpw1, List.pairwise_singleton R w,
           fun a ha b hb => by simp at hb; subst hb; exact hbefore a ha⟩
  · intro a ha b hb
    simp [List.mem_append] at ha
    cases ha with
    | inl h => exact hpw12 a h b hb
    | inr h => simp at h; subst h; exact hafter b hb

/-- Inserting an element preserves the `IsChain R` property under the same conditions. -/
lemma isChain_insertIdx_of_isChain {α : Type*} {R : α → α → Prop} [Trans R R R]
    {l : List α} {w : α} {i : ℕ}
    (hch : l.IsChain R)
    (hi : i ≤ l.length)
    (hbefore : ∀ x ∈ l.take i, R x w)
    (hafter : ∀ y ∈ l.drop i, R w y) :
    (l.insertIdx i w).IsChain R := by
  rw [List.isChain_iff_pairwise] at hch ⊢
  exact pairwise_insertIdx_of_pairwise hch hi hbefore hafter

/-- Hypothesis: a panel (length $n-2$ chain) compatible with a frame can be extended to two
distinct chambers, both containing the panel. -/
structure PanelGapHyp where
  fill_gap : ∀ (F : Frame k n) (panel : SubspaceFlag k n),
    (∀ V ∈ panel.chain, F.IsCompatible k n V) →
    panel.chain.length = n - 2 →
    ∃ (chain₁ chain₂ : List (Submodule k (Vec k n))),
      chain₁ ≠ [] ∧
      chain₁.IsChain (· < ·) ∧
      (∀ V ∈ chain₁, V ≠ ⊥ ∧ V ≠ ⊤) ∧
      chain₁.length = n - 1 ∧
      chain₂ ≠ [] ∧
      chain₂.IsChain (· < ·) ∧
      (∀ V ∈ chain₂, V ≠ ⊥ ∧ V ≠ ⊤) ∧
      chain₂.length = n - 1 ∧
      (∀ V ∈ panel.chain, V ∈ chain₁) ∧
      (∀ V ∈ panel.chain, V ∈ chain₂) ∧
      chain₁ ≠ chain₂


/-- Hypothesis: given a panel and a compatible frame, one can produce two distinct subspaces
$W_1, W_2$ that, when inserted at a common position, each turn the panel into a chamber. -/
structure FrameGapFillerHyp where
  find_and_fill : ∀ (F : Frame k n) (panel : SubspaceFlag k n),
    (∀ V ∈ panel.chain, F.IsCompatible k n V) →
    panel.chain.length = n - 2 →
    ∃ (W₁ W₂ : Submodule k (Vec k n)) (pos : ℕ),
      W₁ ≠ W₂ ∧
      W₁ ≠ ⊥ ∧ W₁ ≠ ⊤ ∧
      W₂ ≠ ⊥ ∧ W₂ ≠ ⊤ ∧
      pos ≤ panel.chain.length ∧
      (panel.chain.insertIdx pos W₁).IsChain (· < ·) ∧
      (panel.chain.insertIdx pos W₁).length = n - 1 ∧
      (panel.chain.insertIdx pos W₂).IsChain (· < ·) ∧
      (panel.chain.insertIdx pos W₂).length = n - 1 ∧
      (∀ V ∈ panel.chain.insertIdx pos W₁, V ≠ ⊥ ∧ V ≠ ⊤) ∧
      (∀ V ∈ panel.chain.insertIdx pos W₂, V ≠ ⊥ ∧ V ≠ ⊤)


/-- Hypothesis: any length-$(n-2)$ chain admits two distinct frame-compatible insertions
$W_1, W_2$ at a common index, sandwiched strictly between the surrounding terms. -/
structure SubmoduleGapInsertionHyp where
  find_gap : ∀ (F : Frame k n) (chain : List (Submodule k (Vec k n))),
    chain.IsChain (· < ·) →
    (∀ V ∈ chain, F.IsCompatible k n V) →
    (∀ V ∈ chain, V ≠ ⊥ ∧ V ≠ ⊤) →
    chain.length = n - 2 →
    ∃ (W₁ W₂ : Submodule k (Vec k n)) (pos : ℕ),
      W₁ ≠ W₂ ∧
      W₁ ≠ ⊥ ∧ W₁ ≠ ⊤ ∧
      W₂ ≠ ⊥ ∧ W₂ ≠ ⊤ ∧
      pos ≤ chain.length ∧
      (∀ x ∈ chain.take pos, x < W₁) ∧
      (∀ y ∈ chain.drop pos, W₁ < y) ∧
      (∀ x ∈ chain.take pos, x < W₂) ∧
      (∀ y ∈ chain.drop pos, W₂ < y)

/-- Hypothesis bundling the bijective correspondence between $F$-compatible subspaces of
$k^n$ and subsets $S \subseteq \{1,\dots,n\}$ via $S \mapsto \bigoplus_{i \in S} L_i$; this
records the extraction, its inverse, strict-monotonicity, and properness preservation. -/
structure FrameFinsetCorrespondenceHyp where
  extract : Frame k n → Submodule k (Vec k n) → Finset (Fin n)
  extract_eq : ∀ (F : Frame k n) (V : Submodule k (Vec k n)),
    F.IsCompatible k n V →
    V = ⨆ i ∈ extract F V, F.lines i
  extract_ssubset : ∀ (F : Frame k n) (V₁ V₂ : Submodule k (Vec k n)),
    F.IsCompatible k n V₁ → F.IsCompatible k n V₂ →
    V₁ < V₂ → extract F V₁ ⊂ extract F V₂
  extract_nonempty : ∀ (F : Frame k n) (V : Submodule k (Vec k n)),
    F.IsCompatible k n V → V ≠ ⊥ → (extract F V).Nonempty
  extract_proper : ∀ (F : Frame k n) (V : Submodule k (Vec k n)),
    F.IsCompatible k n V → V ≠ ⊤ → extract F V ≠ Finset.univ
  lift_ssubset : ∀ (F : Frame k n) (S₁ S₂ : Finset (Fin n)),
    S₁ ⊂ S₂ → (⨆ i ∈ S₁, F.lines i) < (⨆ i ∈ S₂, F.lines i)
  lift_nonempty : ∀ (F : Frame k n) (S : Finset (Fin n)),
    S.Nonempty → (⨆ i ∈ S, F.lines i) ≠ ⊥
  lift_proper : ∀ (F : Frame k n) (S : Finset (Fin n)),
    S ≠ Finset.univ → (⨆ i ∈ S, F.lines i) ≠ ⊤
  lift_ne : ∀ (F : Frame k n) (S₁ S₂ : Finset (Fin n)),
    S₁ ≠ S₂ → (⨆ i ∈ S₁, F.lines i) ≠ (⨆ i ∈ S₂, F.lines i)

/-- Hypothesis: any strictly increasing chain of proper non-empty subsets of $\mathrm{Fin}\ n$
of length $n-2$ admits two distinct insertions at a common position. -/
structure FinsetChainGapHyp where
  find_gap : ∀ (chain : List (Finset (Fin n))),
    chain.IsChain (· ⊂ ·) →
    (∀ S ∈ chain, S.Nonempty) →
    (∀ S ∈ chain, S ≠ Finset.univ) →
    chain.length = n - 2 →
    ∃ (T₁ T₂ : Finset (Fin n)) (pos : ℕ),
      T₁ ≠ T₂ ∧
      T₁.Nonempty ∧ T₁ ≠ Finset.univ ∧
      T₂.Nonempty ∧ T₂ ≠ Finset.univ ∧
      pos ≤ chain.length ∧
      (∀ S ∈ chain.take pos, S ⊂ T₁) ∧
      (∀ S ∈ chain.drop pos, T₁ ⊂ S) ∧
      (∀ S ∈ chain.take pos, S ⊂ T₂) ∧
      (∀ S ∈ chain.drop pos, T₂ ⊂ S)

/-- Lift the finset gap-insertion property to the submodule level via the frame-finset
correspondence, transporting the two distinct insertions along $S \mapsto \bigoplus_{i \in S} L_i$. -/
noncomputable def submoduleGapInsertionOfSubHyps
    (hcorr : FrameFinsetCorrespondenceHyp k n)
    (hgap_finset : FinsetChainGapHyp n) : SubmoduleGapInsertionHyp k n where
  find_gap := fun F chain hchain hcompat hproper hlen => by

    let extractF := hcorr.extract F
    let finset_chain : List (Finset (Fin n)) := chain.map extractF

    have hlen_fc : finset_chain.length = chain.length := List.length_map ..

    have hchain_fc : finset_chain.IsChain (· ⊂ ·) := by
      rw [List.isChain_iff_pairwise] at hchain ⊢
      rw [List.pairwise_map]
      exact hchain.imp_of_mem fun ha hb hab =>
        hcorr.extract_ssubset F _ _ (hcompat _ ha) (hcompat _ hb) hab


    have hne_fc : ∀ S ∈ finset_chain, S.Nonempty := by
      intro S hS
      rw [List.mem_map] at hS
      obtain ⟨V, hV, rfl⟩ := hS
      exact hcorr.extract_nonempty F V (hcompat V hV) (hproper V hV).1

    have hpr_fc : ∀ S ∈ finset_chain, S ≠ Finset.univ := by
      intro S hS
      rw [List.mem_map] at hS
      obtain ⟨V, hV, rfl⟩ := hS
      exact hcorr.extract_proper F V (hcompat V hV) (hproper V hV).2

    have hlen_fc' : finset_chain.length = n - 2 := by rw [hlen_fc, hlen]
    obtain ⟨T₁, T₂, pos, hne, hT₁_ne, hT₁_pr, hT₂_ne, hT₂_pr,
            hpos_fc, hbef₁, haft₁, hbef₂, haft₂⟩ :=
      hgap_finset.find_gap finset_chain hchain_fc hne_fc hpr_fc hlen_fc'

    let W₁ := ⨆ i ∈ T₁, F.lines i
    let W₂ := ⨆ i ∈ T₂, F.lines i
    refine ⟨W₁, W₂, pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

    · exact hcorr.lift_ne F T₁ T₂ hne

    · exact hcorr.lift_nonempty F T₁ hT₁_ne

    · exact hcorr.lift_proper F T₁ hT₁_pr

    · exact hcorr.lift_nonempty F T₂ hT₂_ne

    · exact hcorr.lift_proper F T₂ hT₂_pr

    · rwa [hlen_fc] at hpos_fc

    · intro V hV
      have hV_chain : V ∈ chain := List.mem_of_mem_take hV
      have hextract := hcorr.extract_eq F V (hcompat V hV_chain)
      have hS_V_mem : extractF V ∈ finset_chain.take pos := by
        rw [← List.map_take]
        exact List.mem_map_of_mem (f := extractF) hV
      have hS_V_lt : extractF V ⊂ T₁ := hbef₁ _ hS_V_mem
      rw [hextract]
      exact hcorr.lift_ssubset F _ T₁ hS_V_lt

    · intro V hV
      have hV_chain : V ∈ chain := List.mem_of_mem_drop hV
      have hextract := hcorr.extract_eq F V (hcompat V hV_chain)
      have hS_V_mem : extractF V ∈ finset_chain.drop pos := by
        rw [← List.map_drop]
        exact List.mem_map_of_mem (f := extractF) hV
      have hS_V_lt : T₁ ⊂ extractF V := haft₁ _ hS_V_mem
      rw [hextract]
      exact hcorr.lift_ssubset F T₁ _ hS_V_lt

    · intro V hV
      have hV_chain : V ∈ chain := List.mem_of_mem_take hV
      have hextract := hcorr.extract_eq F V (hcompat V hV_chain)
      have hS_V_mem : extractF V ∈ finset_chain.take pos := by
        rw [← List.map_take]
        exact List.mem_map_of_mem (f := extractF) hV
      have hS_V_lt : extractF V ⊂ T₂ := hbef₂ _ hS_V_mem
      rw [hextract]
      exact hcorr.lift_ssubset F _ T₂ hS_V_lt

    · intro V hV
      have hV_chain : V ∈ chain := List.mem_of_mem_drop hV
      have hextract := hcorr.extract_eq F V (hcompat V hV_chain)
      have hS_V_mem : extractF V ∈ finset_chain.drop pos := by
        rw [← List.map_drop]
        exact List.mem_map_of_mem (f := extractF) hV
      have hS_V_lt : T₂ ⊂ extractF V := haft₂ _ hS_V_mem
      rw [hextract]
      exact hcorr.lift_ssubset F T₂ _ hS_V_lt

/-- Convert a submodule gap-insertion into a frame gap filler: the two distinct insertions
literally produce two distinct chambers via `insertIdx`. -/
noncomputable def frameGapFillerOfGapInsertion
    (hgap : SubmoduleGapInsertionHyp k n) : FrameGapFillerHyp k n where
  find_and_fill := fun F panel hcompat hlen => by
    obtain ⟨W₁, W₂, pos, hne, hW₁_bot, hW₁_top, hW₂_bot, hW₂_top,
            hpos, hbef₁, haft₁, hbef₂, haft₂⟩ :=
      hgap.find_gap F panel.chain panel.chain_strictly_increasing
        hcompat panel.chain_proper hlen
    refine ⟨W₁, W₂, pos, hne, hW₁_bot, hW₁_top, hW₂_bot, hW₂_top, hpos,
            ?_, ?_, ?_, ?_, ?_, ?_⟩

    · exact isChain_insertIdx_of_isChain panel.chain_strictly_increasing hpos hbef₁ haft₁

    · rw [List.length_insertIdx, if_pos hpos, hlen]
      have : 0 < panel.chain.length := List.length_pos_of_ne_nil panel.chain_nonempty
      omega

    · exact isChain_insertIdx_of_isChain panel.chain_strictly_increasing hpos hbef₂ haft₂

    · rw [List.length_insertIdx, if_pos hpos, hlen]
      have : 0 < panel.chain.length := List.length_pos_of_ne_nil panel.chain_nonempty
      omega

    · intro V hV
      rw [List.mem_insertIdx hpos] at hV
      cases hV with
      | inl h => subst h; exact ⟨hW₁_bot, hW₁_top⟩
      | inr h => exact panel.chain_proper V h

    · intro V hV
      rw [List.mem_insertIdx hpos] at hV
      cases hV with
      | inl h => subst h; exact ⟨hW₂_bot, hW₂_top⟩
      | inr h => exact panel.chain_proper V h


/-- Inserting two different elements at the same position yields different lists. -/
lemma insertIdx_ne_of_ne {α : Type*} {l : List α} {a b : α} {i : ℕ}
    (hne : a ≠ b) (hi : i ≤ l.length) :
    l.insertIdx i a ≠ l.insertIdx i b := by
  intro heq
  apply hne
  have hlen : i < (l.insertIdx i a).length := by
    rw [List.length_insertIdx]; split <;> omega
  have ha := List.getElem_insertIdx_self hlen
  have hlen' : i < (l.insertIdx i b).length := by
    rw [List.length_insertIdx]; split <;> omega
  have hb := List.getElem_insertIdx_self hlen'
  have : (l.insertIdx i a)[i]'hlen = (l.insertIdx i b)[i]'hlen' := by
    simp only [heq]
  rw [ha, hb] at this
  exact this


/-- Wrap a `FrameGapFillerHyp` into a `PanelGapHyp` by reading off the two distinct extended
chambers obtained from the insertions $W_1 \ne W_2$. -/
noncomputable def panelGapOfFrameGapFiller
    (filler : FrameGapFillerHyp k n) : PanelGapHyp k n where
  fill_gap := fun F panel hcompat hlen => by
    obtain ⟨W₁, W₂, pos, hne, hW₁_bot, hW₁_top, hW₂_bot, hW₂_top,
            hpos, hch₁, hlen₁, hch₂, hlen₂, hpr₁, hpr₂⟩ :=
      filler.find_and_fill F panel hcompat hlen
    refine ⟨panel.chain.insertIdx pos W₁, panel.chain.insertIdx pos W₂,
            ?_, hch₁, hpr₁, hlen₁, ?_, hch₂, hpr₂, hlen₂, ?_, ?_, ?_⟩
    · intro h; simp [h] at hlen₁
      have : 0 < panel.chain.length := List.length_pos_of_ne_nil panel.chain_nonempty
      omega
    · intro h; simp [h] at hlen₂
      have : 0 < panel.chain.length := List.length_pos_of_ne_nil panel.chain_nonempty
      omega
    · intro V hV; rw [List.mem_insertIdx hpos]; exact Or.inr hV
    · intro V hV; rw [List.mem_insertIdx hpos]; exact Or.inr hV
    · exact insertIdx_ne_of_ne hne hpos


/-- Convert a `PanelGapHyp` into a `DirectPanelExtensionHyp` by packaging the two chains
as `SubspaceFlag`s with the chamber property. -/
noncomputable def directPanelExtensionOfGap
    (gap : PanelGapHyp k n) : DirectPanelExtensionHyp k n where
  extend := fun F panel hcompat hlen => by
    obtain ⟨ch₁, ch₂, hne₁, hch₁, hpr₁, hlen₁,
            hne₂, hch₂, hpr₂, hlen₂, hmem₁, hmem₂, hdist⟩ :=
      gap.fill_gap F panel hcompat hlen
    let C₁ : SubspaceFlag k n :=
      { chain := ch₁
        chain_nonempty := hne₁
        chain_strictly_increasing := hch₁
        chain_proper := hpr₁ }
    let C₂ : SubspaceFlag k n :=
      { chain := ch₂
        chain_nonempty := hne₂
        chain_strictly_increasing := hch₂
        chain_proper := hpr₂ }
    have hchamber₁ : IsChamber k n C₁ := hlen₁
    have hchamber₂ : IsChamber k n C₂ := hlen₂
    have hne : C₁ ≠ C₂ := by
      intro heq; apply hdist; exact congrArg SubspaceFlag.chain heq
    exact ⟨C₁, C₂, hchamber₁, hchamber₂, hne, hmem₁, hmem₂⟩

end GLnBuilding
