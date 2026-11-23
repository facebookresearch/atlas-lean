/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleFunctorDefs

set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

/-- The module category `M` is nonzero: it contains some object that is not initial. -/
class NonzeroModuleCategory (M : Type u₂) [Category.{v₂} M] : Prop where
  exists_nonzero : ∃ (X : M), IsEmpty (IsInitial X)

/-- Data witnessing the internal-Hom adjunction `Hom(X ⊗ m, n) ≃ Hom(X, iHom m n)` together
with the second-variable exactness assumption that `iHom m -` preserves both monos and epis. -/
structure InternalHomExactInSecondVar
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] where
  iHom : M → M → C
  iHomEquiv : ∀ (X : C) (m n : M), (X ⊗ᵐ m ⟶ n) ≃ (X ⟶ iHom m n)
  iHomMap : ∀ (m : M) {n₁ n₂ : M}, (n₁ ⟶ n₂) → (iHom m n₁ ⟶ iHom m n₂)
  preserves_mono : ∀ (m : M) {n₁ n₂ : M} (f : n₁ ⟶ n₂), Mono f → Mono (iHomMap m f)
  preserves_epi : ∀ (m : M) {n₁ n₂ : M} (f : n₁ ⟶ n₂), Epi f → Epi (iHomMap m f)
  iHomEquiv_natural : ∀ (X : C) (m : M) {n₁ n₂ : M} (g : X ⊗ᵐ m ⟶ n₁) (f : n₁ ⟶ n₂),
    iHomEquiv X m n₂ (g ≫ f) = (iHomEquiv X m n₁ g) ≫ (iHomMap m f)

/-- Proposition 2.10.7(1): If the internal Hom `Hom(N, -) : M → C` is exact in the second
variable, then the module category `M` over `C` is exact. -/
@[reducible] def prop_2_10_7_hom_exact_implies_exact
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    [LeftModuleCategory C M]
    (h : InternalHomExactInSecondVar C M) :
    ExactModuleCategory C M :=
  { (‹LeftModuleCategory C M›) with
    action_preserves_projective := fun P N _ => by
      constructor
      intro A B f e _


      let f' : P ⟶ h.iHom N B := h.iHomEquiv P N B f

      have hEpi : Epi (h.iHomMap N e) := h.preserves_epi N e inferInstance

      obtain ⟨g', hg'⟩ := Projective.factors f' (h.iHomMap N e)


      let g : P ⊗ᵐ N ⟶ A := (h.iHomEquiv P N A).symm g'
      use g

      apply (h.iHomEquiv P N B).injective

      rw [h.iHomEquiv_natural P N g e]

      simp only [g, Equiv.apply_symm_apply]
      exact hg' }

/-- The internal-Hom data of a left `C`-module category `M` without any exactness conditions:
the adjunction `Hom(X ⊗ m, n) ≃ Hom(X, iHom m n)` along with naturality. -/
structure ModuleInternalHomData
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] where
  iHom : M → M → C
  iHomEquiv : ∀ (X : C) (m n : M), (X ⊗ᵐ m ⟶ n) ≃ (X ⟶ iHom m n)
  iHomMap : ∀ (m : M) {n₁ n₂ : M}, (n₁ ⟶ n₂) → (iHom m n₁ ⟶ iHom m n₂)
  iHomEquiv_natural : ∀ (X : C) (m : M) {n₁ n₂ : M} (g : X ⊗ᵐ m ⟶ n₁) (f : n₁ ⟶ n₂),
    iHomEquiv X m n₂ (g ≫ f) = (iHomEquiv X m n₁ g) ≫ (iHomMap m f)





/-- Restatement of Proposition 2.10.7(1) as an alias of `prop_2_10_7_hom_exact_implies_exact`. -/
abbrev proposition_2_10_7_part1
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    [LeftModuleCategory C M]
    (h : InternalHomExactInSecondVar C M) :
    ExactModuleCategory C M :=
  prop_2_10_7_hom_exact_implies_exact h


/-- Proposition 2.10.7: combined statement, defaulting to the first part. -/
@[reducible] noncomputable def proposition_2_10_7
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    [LeftModuleCategory C M]
    (h : InternalHomExactInSecondVar C M) :
    ExactModuleCategory C M :=
  proposition_2_10_7_part1 h

end CategoryTheory
