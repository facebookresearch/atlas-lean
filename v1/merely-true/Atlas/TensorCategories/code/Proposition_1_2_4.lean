/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A version of "unit object" data: an object `U` together with natural isomorphisms
identifying `tensorLeft U` and `tensorRight U` with the identity functor, and satisfying the
triangle axiom relating them via the associator. -/
structure IsUnitObject' (U : C) where
  rightUnitor' : tensorRight U ≅ Functor.id C
  leftUnitor' : tensorLeft U ≅ Functor.id C
  triangle' : ∀ (X Y : C),
    (α_ X U Y).hom ≫ X ◁ (leftUnitor'.hom.app Y) = (rightUnitor'.hom.app X) ▷ Y

/-- The canonical unit object `𝟙_ C` together with its left/right unitors satisfies the
`IsUnitObject'` predicate. -/
noncomputable def unitIsUnitObject' : IsUnitObject' (𝟙_ C) (C := C) where
  rightUnitor' := NatIso.ofComponents (fun X => ρ_ X) (by aesop_cat)
  leftUnitor' := NatIso.ofComponents (fun X => λ_ X) (by aesop_cat)
  triangle' := fun X Y => by simp [NatIso.ofComponents]

/-- For any object `U` equipped with a unit structure `hU : IsUnitObject' U`, there is a
canonical isomorphism `𝟙_ C ≅ U` constructed from the right-unitor of `hU` and the standard
left-unitor of `𝟙_ C`. -/
noncomputable def unit_object_iso' (U : C) (hU : IsUnitObject' U) : 𝟙_ C ≅ U :=
  (hU.rightUnitor'.app (𝟙_ C)).symm ≪≫ (λ_ U)

/-- Any isomorphism `b : 𝟙_ C ⟶ 𝟙_ C` that is compatible with the right unitor in the sense
that `(b ⊗ b) ≫ ρ = ρ ≫ b` must be the identity. -/
theorem unit_endo_compat_is_id' (b : 𝟙_ C ⟶ 𝟙_ C) [IsIso b]
    (hb : (b ⊗ₘ b) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ b) :
    b = 𝟙 (𝟙_ C) := by


  have nat_b : b ▷ 𝟙_ C ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ b :=
    rightUnitor_naturality b


  have h_tensor_eq_whisk : b ⊗ₘ b = b ▷ 𝟙_ C := by
    have : (b ⊗ₘ b) ≫ (ρ_ (𝟙_ C)).hom = (b ▷ 𝟙_ C) ≫ (ρ_ (𝟙_ C)).hom := by
      rw [hb, nat_b]
    exact (cancel_mono (ρ_ (𝟙_ C)).hom).mp this

  have h_def : b ⊗ₘ b = b ▷ 𝟙_ C ≫ 𝟙_ C ◁ b :=
    MonoidalCategory.tensorHom_def b b

  have h_comp : b ▷ 𝟙_ C ≫ 𝟙_ C ◁ b = b ▷ 𝟙_ C := by
    rw [← h_def, h_tensor_eq_whisk]


  have h_whisk_id : 𝟙_ C ◁ b = 𝟙 (𝟙_ C ⊗ 𝟙_ C) := by
    rw [← cancel_epi (b ▷ 𝟙_ C)]
    rw [h_comp, Category.comp_id]


  have h_lambda : (λ_ (𝟙_ C)).hom ≫ b = (λ_ (𝟙_ C)).hom := by
    rw [← leftUnitor_naturality b, h_whisk_id, Category.id_comp]

  exact (cancel_epi (λ_ (𝟙_ C)).hom).mp (by rw [h_lambda, Category.comp_id])

/-- Uniqueness part of Proposition 1.2.4: two isomorphisms `f, g : 𝟙_ C ≅ U` compatible
with the right unitor of a unit object `U` must agree. -/
theorem unit_iso_compatible_unique' (U : C) (hU : IsUnitObject' U)
    (f g : 𝟙_ C ≅ U)
    (hf : (f.hom ⊗ₘ f.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ f.hom)
    (hg : (g.hom ⊗ₘ g.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ g.hom) :
    f = g := by
  let r'_U : U ⊗ U ⟶ U := hU.rightUnitor'.hom.app U
  change (f.hom ⊗ₘ f.hom) ≫ r'_U = (ρ_ (𝟙_ C)).hom ≫ f.hom at hf
  change (g.hom ⊗ₘ g.hom) ≫ r'_U = (ρ_ (𝟙_ C)).hom ≫ g.hom at hg
  ext
  suffices h : f.hom ≫ g.inv = 𝟙 (𝟙_ C) by
    have := congr_arg (· ≫ g.hom) h
    simp at this
    exact this
  apply unit_endo_compat_is_id'
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  have cancel_g : r'_U ≫ g.inv = (g.inv ⊗ₘ g.inv) ≫ (ρ_ (𝟙_ C)).hom := by
    rw [← cancel_epi (g.hom ⊗ₘ g.hom)]
    rw [← Category.assoc, hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  have hf_ginv : (f.hom ⊗ₘ f.hom) ≫ r'_U ≫ g.inv = (ρ_ (𝟙_ C)).hom ≫ f.hom ≫ g.inv := by
    rw [← Category.assoc, hf, Category.assoc]
  rw [Category.assoc, ← cancel_g]
  exact hf_ginv

/-- Proposition 1.2.4: The unit object in a monoidal category is unique up to a unique
isomorphism compatible with the right unitor. -/
theorem Proposition_1_2_4 (U : C) (hU : IsUnitObject' U) :
    Nonempty (𝟙_ C ≅ U) ∧
    (∀ (f g : 𝟙_ C ≅ U),
      (f.hom ⊗ₘ f.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ f.hom →
      (g.hom ⊗ₘ g.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ g.hom →
      f = g) :=
  ⟨⟨unit_object_iso' U hU⟩,
   fun f g hf hg => unit_iso_compatible_unique' U hU f g hf hg⟩

end CategoryTheory
