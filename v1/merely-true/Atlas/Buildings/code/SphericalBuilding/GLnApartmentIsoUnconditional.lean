/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLnInstance
import Atlas.Buildings.code.SphericalBuilding.FinsetGapCorrespondenceProof

set_option maxHeartbeats 1600000

namespace GLnBuilding

open scoped Classical

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}


/-- Frame-indexed join: $\mathrm{joinSub}\ F\ S = \bigoplus_{i \in S} F.\mathrm{lines}\ i$. -/
def joinSub (F : Frame k n) (S : Finset (Fin n)) : Submodule k (Vec k n) :=
  ⨆ i ∈ S, F.lines i

/-- The map $S \mapsto \mathrm{joinSub}\ F\ S$ is injective. -/
theorem joinSub_injective (F : Frame k n) : Function.Injective (joinSub F) := by
  intro S₁ S₂ h; by_contra hne; exact frame_biSup_injective k n F hne h

/-- Every `joinSub F S` is $F$-compatible by definition. -/
theorem joinSub_isCompatible (F : Frame k n) (S : Finset (Fin n)) :
    F.IsCompatible k n (joinSub F S) := ⟨S, rfl⟩

/-- Round-trip identity: `extractFinset F (joinSub F S) = S`. -/
theorem extractFinset_of_joinSub (F : Frame k n) (S : Finset (Fin n)) :
    extractFinset k n F (joinSub F S) = S := by
  have hcompat : F.IsCompatible k n (joinSub F S) := joinSub_isCompatible F S
  have hspec := extractFinset_spec k n F (joinSub F S) hcompat
  have : joinSub F (extractFinset k n F (joinSub F S)) = joinSub F S := hspec.symm
  exact joinSub_injective F this

/-- Round-trip identity: `joinSub F (extractFinset F V) = V` for any $F$-compatible $V$. -/
theorem joinSub_extractFinset (F : Frame k n) (V : Submodule k (Vec k n))
    (h : F.IsCompatible k n V) : joinSub F (extractFinset k n F V) = V :=
  (extractFinset_spec k n F V h).symm


/-- Unconditional construction of the apartment isomorphism: given two apartments sharing
two chambers, build a bijection $f$ on subspaces that sends $F_1$-compatible subspaces to
$F_2$-compatible ones, fixes the shared chambers, and is the identity on the intersection. The
construction matches "only-$F_1$" finsets bijectively to "only-$F_2$" finsets via a cardinality
argument. -/
noncomputable def apartmentIsoHypUnconditional (k : Type*) [Field k] (n : ℕ) :
    ApartmentIsoHyp k n where
  iso_apartments := by
    intro F₁ F₂ C₁ C₂ hC₁ hC₂ hC₁F₁ hC₂F₁ hC₁F₂ hC₂F₂


    let onlyF₁ : Finset (Finset (Fin n)) :=
      Finset.univ.filter (fun S => ¬ F₂.IsCompatible k n (joinSub F₁ S))
    let onlyF₂ : Finset (Finset (Fin n)) :=
      Finset.univ.filter (fun S => ¬ F₁.IsCompatible k n (joinSub F₂ S))
    let bothF₁ : Finset (Finset (Fin n)) :=
      Finset.univ.filter (fun S => F₂.IsCompatible k n (joinSub F₁ S))
    let bothF₂ : Finset (Finset (Fin n)) :=
      Finset.univ.filter (fun S => F₁.IsCompatible k n (joinSub F₂ S))


    have card_onlyF₁_eq : onlyF₁.card = onlyF₂.card := by
      have huniv₁ : onlyF₁.card + bothF₁.card =
          (Finset.univ : Finset (Finset (Fin n))).card := by
        show (Finset.univ.filter (fun S => ¬ F₂.IsCompatible k n (joinSub F₁ S))).card +
          (Finset.univ.filter (fun S => F₂.IsCompatible k n (joinSub F₁ S))).card =
          Finset.univ.card
        rw [add_comm]
        exact Finset.card_filter_add_card_filter_not _
      have huniv₂ : onlyF₂.card + bothF₂.card =
          (Finset.univ : Finset (Finset (Fin n))).card := by
        show (Finset.univ.filter (fun S => ¬ F₁.IsCompatible k n (joinSub F₂ S))).card +
          (Finset.univ.filter (fun S => F₁.IsCompatible k n (joinSub F₂ S))).card =
          Finset.univ.card
        rw [add_comm]
        exact Finset.card_filter_add_card_filter_not _

      have hboth : bothF₁.card = bothF₂.card := by
        apply le_antisymm
        ·
          let g₁ : ↥bothF₁ → ↥bothF₂ := fun ⟨S, hS⟩ =>
            let h := (Finset.mem_filter.mp hS).2

            let T := Classical.choose h


            have hTeq : joinSub F₁ S = joinSub F₂ T := by
              exact Classical.choose_spec h
            ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ T,
              ⟨S, hTeq.symm⟩⟩⟩
          have g₁_inj : Function.Injective g₁ := by
            intro ⟨S₁, hS₁⟩ ⟨S₂, hS₂⟩ heq
            simp only [g₁, Subtype.mk.injEq] at heq
            have h₁ := (Finset.mem_filter.mp hS₁).2
            have h₂ := (Finset.mem_filter.mp hS₂).2
            have hTeq₁ : joinSub F₁ S₁ = joinSub F₂ (Classical.choose h₁) := by
              exact Classical.choose_spec h₁
            have hTeq₂ : joinSub F₁ S₂ = joinSub F₂ (Classical.choose h₂) := by
              exact Classical.choose_spec h₂
            have : joinSub F₁ S₁ = joinSub F₁ S₂ := by
              rw [hTeq₁, hTeq₂, heq]
            exact Subtype.ext (joinSub_injective F₁ this)
          calc bothF₁.card = Fintype.card ↥bothF₁ := (Fintype.card_coe bothF₁).symm
            _ ≤ Fintype.card ↥bothF₂ := Fintype.card_le_of_injective g₁ g₁_inj
            _ = bothF₂.card := Fintype.card_coe bothF₂
        ·
          let g₂ : ↥bothF₂ → ↥bothF₁ := fun ⟨T, hT⟩ =>
            let h := (Finset.mem_filter.mp hT).2
            let S := Classical.choose h
            have hSeq : joinSub F₂ T = joinSub F₁ S := by
              exact Classical.choose_spec h
            ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S,
              ⟨T, hSeq.symm⟩⟩⟩
          have g₂_inj : Function.Injective g₂ := by
            intro ⟨T₁, hT₁⟩ ⟨T₂, hT₂⟩ heq
            simp only [g₂, Subtype.mk.injEq] at heq
            have h₁ := (Finset.mem_filter.mp hT₁).2
            have h₂ := (Finset.mem_filter.mp hT₂).2
            have hSeq₁ : joinSub F₂ T₁ = joinSub F₁ (Classical.choose h₁) := by
              exact Classical.choose_spec h₁
            have hSeq₂ : joinSub F₂ T₂ = joinSub F₁ (Classical.choose h₂) := by
              exact Classical.choose_spec h₂
            have : joinSub F₂ T₁ = joinSub F₂ T₂ := by
              rw [hSeq₁, hSeq₂, heq]
            exact Subtype.ext (joinSub_injective F₂ this)
          calc bothF₂.card = Fintype.card ↥bothF₂ := (Fintype.card_coe bothF₂).symm
            _ ≤ Fintype.card ↥bothF₁ := Fintype.card_le_of_injective g₂ g₂_inj
            _ = bothF₁.card := Fintype.card_coe bothF₁
      omega


    have hcard' : Fintype.card ↥onlyF₁ = Fintype.card ↥onlyF₂ := by
      simp only [Fintype.card_coe]; exact card_onlyF₁_eq
    let σ : ↥onlyF₁ ≃ ↥onlyF₂ := Fintype.equivOfCardEq hcard'


    have mem_onlyF₁ : ∀ V, F₁.IsCompatible k n V → ¬F₂.IsCompatible k n V →
        extractFinset k n F₁ V ∈ onlyF₁ := by
      intro V h₁ h₂
      simp only [onlyF₁, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rwa [joinSub_extractFinset F₁ V h₁]⟩

    have mem_onlyF₂ : ∀ V, F₂.IsCompatible k n V → ¬F₁.IsCompatible k n V →
        extractFinset k n F₂ V ∈ onlyF₂ := by
      intro V h₂ h₁
      simp only [onlyF₂, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rwa [joinSub_extractFinset F₂ V h₂]⟩


    let f : Submodule k (Vec k n) → Submodule k (Vec k n) := fun V =>
      if h₁ : F₁.IsCompatible k n V then
        if h₂ : F₂.IsCompatible k n V then V
        else joinSub F₂ (σ ⟨extractFinset k n F₁ V, mem_onlyF₁ V h₁ h₂⟩).val
      else if h₂ : F₂.IsCompatible k n V then
        joinSub F₁ (σ.symm ⟨extractFinset k n F₂ V, mem_onlyF₂ V h₂ h₁⟩).val
      else V


    have inv_F1_only : ∀ V, ∀ (h₁ : F₁.IsCompatible k n V) (h₂ : ¬F₂.IsCompatible k n V),
        let S := extractFinset k n F₁ V
        let idx : ↥onlyF₁ := ⟨S, mem_onlyF₁ V h₁ h₂⟩
        let T_idx := σ idx
        let T := T_idx.val

        ¬F₁.IsCompatible k n (joinSub F₂ T) ∧
        F₂.IsCompatible k n (joinSub F₂ T) ∧
        (σ.symm ⟨extractFinset k n F₂ (joinSub F₂ T),
          mem_onlyF₂ _ (joinSub_isCompatible F₂ T)
            (by have := T_idx.property
                simp only [onlyF₂, Finset.mem_filter] at this
                exact this.2)⟩).val = S := by
      intro V h₁ h₂
      simp only
      constructor
      · have := (σ ⟨extractFinset k n F₁ V, mem_onlyF₁ V h₁ h₂⟩).property
        simp only [onlyF₂, Finset.mem_filter] at this
        exact this.2
      constructor
      · exact joinSub_isCompatible F₂ _
      · set idx₁ := (⟨extractFinset k n F₁ V, mem_onlyF₁ V h₁ h₂⟩ : ↥onlyF₁)
        set idx₂ := σ idx₁
        have hext : extractFinset k n F₂ (joinSub F₂ idx₂.val) = idx₂.val :=
          extractFinset_of_joinSub F₂ _
        have hmem : extractFinset k n F₂ (joinSub F₂ idx₂.val) ∈ onlyF₂ := by
          rw [hext]; exact idx₂.property
        have hsub : (⟨extractFinset k n F₂ (joinSub F₂ idx₂.val), hmem⟩ : ↥onlyF₂) = idx₂ :=
          Subtype.ext hext
        rw [hsub]
        exact congrArg Subtype.val (Equiv.symm_apply_apply σ _)

    refine ⟨f, ?_, ?_, ?_, ?_⟩

    ·
      rw [Function.bijective_iff_has_inverse]
      let g : Submodule k (Vec k n) → Submodule k (Vec k n) := fun V =>
        if h₂ : F₂.IsCompatible k n V then
          if h₁ : F₁.IsCompatible k n V then V
          else joinSub F₁ (σ.symm ⟨extractFinset k n F₂ V, mem_onlyF₂ V h₂ h₁⟩).val
        else if h₁ : F₁.IsCompatible k n V then
          joinSub F₂ (σ ⟨extractFinset k n F₁ V, mem_onlyF₁ V h₁ (by assumption)⟩).val
        else V

      refine ⟨g, ?_, ?_⟩

      ·
        intro V; show g (f V) = V
        simp only [f]
        by_cases h₁ : F₁.IsCompatible k n V
        ·
          by_cases h₂ : F₂.IsCompatible k n V
          ·
            simp only [dif_pos h₁, dif_pos h₂]
            simp only [g, dif_pos h₂, dif_pos h₁]
          ·
            simp only [dif_pos h₁, dif_neg h₂]
            obtain ⟨h₁', h₂', hkey⟩ := inv_F1_only V h₁ h₂
            simp only [g, dif_pos h₂', dif_neg h₁']
            rw [show (σ.symm ⟨extractFinset k n F₂
                  (joinSub F₂ (σ ⟨extractFinset k n F₁ V, mem_onlyF₁ V h₁ h₂⟩).val),
                  _⟩).val = extractFinset k n F₁ V from hkey]
            exact joinSub_extractFinset F₁ V h₁
        ·
          simp only [dif_neg h₁]
          by_cases h₂ : F₂.IsCompatible k n V
          ·
            simp only [dif_pos h₂]

            set T := extractFinset k n F₂ V
            set idx : ↥onlyF₂ := ⟨T, mem_onlyF₂ V h₂ h₁⟩
            set S_idx := σ.symm idx
            set S := S_idx.val
            have hS_in_onlyF₁ := S_idx.property
            simp only [onlyF₁, Finset.mem_filter] at hS_in_onlyF₁
            have h₂' : ¬F₂.IsCompatible k n (joinSub F₁ S) := hS_in_onlyF₁.2
            have h₁' : F₁.IsCompatible k n (joinSub F₁ S) := joinSub_isCompatible F₁ S
            simp only [g, dif_neg h₂', dif_pos h₁']
            show joinSub F₂ (σ ⟨extractFinset k n F₁ (joinSub F₁ S), _⟩).val = V
            have hext : extractFinset k n F₁ (joinSub F₁ S) = S := extractFinset_of_joinSub F₁ S
            have hsub : (⟨extractFinset k n F₁ (joinSub F₁ S),
                mem_onlyF₁ (joinSub F₁ S) h₁' h₂'⟩ : ↥onlyF₁) = S_idx :=
              Subtype.ext hext
            rw [show (σ ⟨extractFinset k n F₁ (joinSub F₁ S),
                mem_onlyF₁ (joinSub F₁ S) h₁' h₂'⟩).val = T from by
              rw [hsub]; exact congrArg Subtype.val (Equiv.apply_symm_apply σ idx)]
            exact joinSub_extractFinset F₂ V h₂
          ·
            simp only [dif_neg h₂]
            simp only [g, dif_neg h₂, dif_neg h₁]

      ·
        intro V; show f (g V) = V
        simp only [g]
        by_cases h₂ : F₂.IsCompatible k n V
        · by_cases h₁ : F₁.IsCompatible k n V
          ·
            simp only [dif_pos h₂, dif_pos h₁]
            simp only [f, dif_pos h₁, dif_pos h₂]
          ·
            simp only [dif_pos h₂, dif_neg h₁]
            set T := extractFinset k n F₂ V
            set idx : ↥onlyF₂ := ⟨T, mem_onlyF₂ V h₂ h₁⟩
            set S_idx := σ.symm idx
            set S := S_idx.val
            have hS_in_onlyF₁ := S_idx.property
            simp only [onlyF₁, Finset.mem_filter] at hS_in_onlyF₁
            have h₂' : ¬F₂.IsCompatible k n (joinSub F₁ S) := hS_in_onlyF₁.2
            have h₁' : F₁.IsCompatible k n (joinSub F₁ S) := joinSub_isCompatible F₁ S
            simp only [f, dif_pos h₁', dif_neg h₂']
            show joinSub F₂ (σ ⟨extractFinset k n F₁ (joinSub F₁ S), _⟩).val = V
            have hext : extractFinset k n F₁ (joinSub F₁ S) = S := extractFinset_of_joinSub F₁ S
            have hsub : (⟨extractFinset k n F₁ (joinSub F₁ S),
                mem_onlyF₁ (joinSub F₁ S) h₁' h₂'⟩ : ↥onlyF₁) = S_idx :=
              Subtype.ext hext
            rw [show (σ ⟨extractFinset k n F₁ (joinSub F₁ S),
                mem_onlyF₁ (joinSub F₁ S) h₁' h₂'⟩).val = T from by
              rw [hsub]; exact congrArg Subtype.val (Equiv.apply_symm_apply σ idx)]
            exact joinSub_extractFinset F₂ V h₂
        · by_cases h₁ : F₁.IsCompatible k n V
          ·
            simp only [dif_neg h₂, dif_pos h₁]
            obtain ⟨h₁', h₂', hkey⟩ := inv_F1_only V h₁ h₂
            simp only [f, dif_neg h₁', dif_pos h₂']
            rw [show (σ.symm ⟨extractFinset k n F₂
                  (joinSub F₂ (σ ⟨extractFinset k n F₁ V, mem_onlyF₁ V h₁ h₂⟩).val),
                  _⟩).val = extractFinset k n F₁ V from hkey]
            exact joinSub_extractFinset F₁ V h₁
          ·
            simp only [dif_neg h₂, dif_neg h₁]
            simp only [f, dif_neg h₁, dif_neg h₂]

    ·
      intro V h₁
      simp only [f, dif_pos h₁]
      by_cases h₂ : F₂.IsCompatible k n V
      · simp only [dif_pos h₂]; exact h₂
      · simp only [dif_neg h₂]; exact joinSub_isCompatible F₂ _

    ·
      intro V hV
      simp only [f, dif_pos (hC₁F₁ V hV), dif_pos (hC₁F₂ V hV)]

    ·
      intro V hV
      simp only [f, dif_pos (hC₂F₁ V hV), dif_pos (hC₂F₂ V hV)]

end

end GLnBuilding
