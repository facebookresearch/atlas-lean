/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ExactModuleCategory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]

/-- Lemma 2.7.1 (EGNO): If `C` has enough projectives and the action preserves epis on
the first variable, then any exact module category over `C` also has enough projectives.-/
theorem Lemma_2_7_1
    [EnoughProjectives C]
    (hEpi : ∀ {X Y : C} (f : X ⟶ Y) (N : M), Epi f → Epi (f ▷ᵐ N)) :
    EnoughProjectives M :=
  ExactModuleCategory.enoughProjectives_of_exact hEpi

end CategoryTheory
