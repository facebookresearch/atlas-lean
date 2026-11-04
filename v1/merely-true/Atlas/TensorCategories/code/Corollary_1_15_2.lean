/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.UnitSemisimplicity.UnitSimple

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u

noncomputable section

/-- Corollary 1.15.2 (EGNO): in any multiring category `C`, the unit object `1` is
isomorphic to a direct sum of pairwise non-isomorphic indecomposable objects. -/
theorem Corollary_1_15_2 (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [TensorCategories.MonoidalBiexact C]
    [IsArtinianRing (End (𝟙_ C))] :
    ∃ (n : ℕ) (f : Fin n → C) (hbp : HasBiproduct f),
      (∀ i, Indecomposable (f i)) ∧
      (∀ i j, i ≠ j → ¬Nonempty (f i ≅ f j)) ∧
      Nonempty (𝟙_ C ≅ @biproduct _ _ _ _ f hbp) :=
  TensorCategories.unit_indecomposable_decomposition TensorCategories.endUnit_isSemisimpleRing

end
