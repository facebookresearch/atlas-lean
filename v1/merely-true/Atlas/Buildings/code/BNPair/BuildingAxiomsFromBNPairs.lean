/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Basic
import Atlas.Buildings.code.BNPair.ParabolicDefs
import Atlas.Buildings.code.BNPair.BuildingsFromBNPairs

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} [DecidableEq B_idx] {M : CoxeterMatrix B_idx}

namespace BNPair

/-- Composition of two left-multiplication maps on a subset $S$ collapses to multiplication by the product. -/
lemma image_mul_left_comp' (a b : G) (S : Set G) :
    (fun x => a * x) '' ((fun x => b * x) '' S) = (fun x => a * b * x) '' S := by
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by group⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨b * z, ⟨z, hz, rfl⟩, by group⟩

/-- Building axiom (B2) at the coset level: if two translated apartments around $g, h$ share a
chamber $C$, then there exists $t \in G$ carrying the $g$-apartment into the $h$-apartment
while fixing $C$ setwise, i.e. $tC = C$ and $t \cdot \mathcal{A}_g \subseteq \mathcal{A}_h$. -/
theorem building_axiom_B2_cosets (bp : BNPair G M) (bd : BruhatProperties bp)
    (ax : BNPairAxioms bp)
    (g h : G)
    (C : Set G)
    (hCg : C ∈ bp.translatedApartmentCosets g)
    (hCh : C ∈ bp.translatedApartmentCosets h) :
    ∃ (t : G),
      (∀ X ∈ bp.translatedApartmentCosets g,
        (fun x => t * x) '' X ∈ bp.translatedApartmentCosets h) ∧
      ((fun x => t * x) '' C = C) := by

  obtain ⟨n₁, hCg'⟩ := hCg
  obtain ⟨n₂, hCh'⟩ := hCh

  refine ⟨h * ↑n₂ * (↑n₁)⁻¹ * g⁻¹, ?_, ?_⟩
  ·
    intro X hX
    obtain ⟨n, rfl⟩ := hX

    rw [leftCoset_left_action]

    have hcalc : h * ↑n₂ * (↑n₁)⁻¹ * g⁻¹ * (g * ↑n) = h * (↑n₂ * (↑n₁)⁻¹ * ↑n) := by group
    rw [hcalc]

    exact ⟨⟨↑n₂ * (↑n₁)⁻¹ * ↑n,
      bp.N.mul_mem (bp.N.mul_mem n₂.2 (bp.N.inv_mem n₁.2)) n.2⟩, rfl⟩
  ·

    rw [hCg', leftCoset_left_action]

    have hcalc : h * ↑n₂ * (↑n₁)⁻¹ * g⁻¹ * (g * ↑n₁) = h * ↑n₂ := by group
    rw [hcalc]

    exact hCh'.symm.trans hCg'

end BNPair
