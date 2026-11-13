/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory CategoryTheory.Limits

namespace SecondIsomorphism

variable {C : Type*} [Category C] [Abelian C]

section

variable {A B X : C} (f : A ⟶ X) (g : B ⟶ X)

/-- For morphisms `f : A ⟶ X` and `g : B ⟶ X` in an abelian category, the two compositions
out of `kernel (biprod.desc f g)` through the biproduct projections satisfy the pullback
square condition (up to a sign on the second leg). This is the equation that lets us
identify the kernel of `f - g : A ⊕ B → X` with the pullback `A ×_X B`. -/
lemma kernelDesc_pullback_condition :
    (kernel.ι (biprod.desc f g) ≫ biprod.fst) ≫ f =
    (-(kernel.ι (biprod.desc f g) ≫ biprod.snd)) ≫ g := by
  simp only [Preadditive.neg_comp, Category.assoc]
  suffices kernel.ι (biprod.desc f g) ≫ biprod.fst ≫ f +
      kernel.ι (biprod.desc f g) ≫ biprod.snd ≫ g = 0 by
    exact eq_neg_of_add_eq_zero_left this
  rw [← Preadditive.comp_add]; convert kernel.condition (biprod.desc f g) using 2
  have t := biprod.total (X := A) (Y := B)
  calc biprod.fst ≫ f + biprod.snd ≫ g
      = biprod.fst ≫ (biprod.inl ≫ biprod.desc f g) +
        biprod.snd ≫ (biprod.inr ≫ biprod.desc f g) := by
          rw [biprod.inl_desc, biprod.inr_desc]
    _ = (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ biprod.desc f g := by
          rw [Preadditive.add_comp, Category.assoc, Category.assoc]
    _ = biprod.desc f g := by rw [t, Category.id_comp]

variable [Mono f] [Mono g]

/-- For monomorphisms `f : A ↪ X` and `g : B ↪ X` in an abelian category, the pullback
`A ×_X B` is canonically isomorphic to the kernel of `biprod.desc f g : A ⊕ B ⟶ X`. This is
the standard identification of intersections of subobjects via biproducts. -/
noncomputable def pullbackIsoKernelOfDesc :
    pullback f g ≅ kernel (biprod.desc f g) where
  hom := kernel.lift _ (biprod.lift (pullback.fst f g) (-pullback.snd f g)) (by
    simp only [biprod.lift_desc, Preadditive.neg_comp, pullback.condition, add_neg_cancel])
  inv := pullback.lift (kernel.ι _ ≫ biprod.fst) (-(kernel.ι _ ≫ biprod.snd))
    (kernelDesc_pullback_condition f g)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst (f := f) (g := g),
        kernel.lift_ι_assoc, biprod.lift_fst]
    · simp only [Category.assoc, Category.id_comp, pullback.lift_snd (f := f) (g := g)]
      rw [Preadditive.comp_neg, kernel.lift_ι_assoc, biprod.lift_snd, neg_neg]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι (biprod.desc f g))).mp
    simp only [Category.assoc, Category.id_comp, kernel.lift_ι]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst,
        pullback.lift_fst (f := f) (g := g)]
    · simp only [Category.assoc, biprod.lift_snd,
        pullback.lift_snd (f := f) (g := g), Preadditive.comp_neg, neg_neg]

omit [Mono f] [Mono g] in
/-- The forward direction of `pullbackIsoKernelOfDesc`, composed with the kernel inclusion,
is the biproduct lift `⟨π₁, −π₂⟩` of the pullback projections. -/
lemma pullbackIsoKernelOfDesc_hom_ι :
    (pullbackIsoKernelOfDesc f g).hom ≫ kernel.ι _ =
      biprod.lift (pullback.fst f g) (-pullback.snd f g) :=
  kernel.lift_ι _ _ _

set_option maxHeartbeats 800000 in
set_option linter.unusedSectionVars false in
/-- **Second isomorphism / pullback-pushout square.** In an abelian category, for
monomorphisms `f : A ↪ X` and `g : B ↪ X`, the square
```
A ×_X B ─→ A
   │        │
   ↓        ↓
   B ───→ image(f ⊕ g)
```
formed by the pullback projections and the canonical maps from `A` and `B` to the image
of `biprod.desc f g` is a pushout. Equivalently, the image of `A ⊕ B → X` is the pushout
`A ⊔_{A ∩ B} B` of subobjects, exhibiting the second isomorphism theorem at the level of
subobjects of `X`. -/
theorem isPushout_pullback_image :
    IsPushout (pullback.fst f g) (pullback.snd f g)
      (biprod.inl ≫ factorThruImage (biprod.desc f g))
      (biprod.inr ≫ factorThruImage (biprod.desc f g)) := by
  have w : pullback.fst f g ≫ biprod.inl ≫ factorThruImage (biprod.desc f g) =
      pullback.snd f g ≫ biprod.inr ≫ factorThruImage (biprod.desc f g) := by
    apply (cancel_mono (image.ι (biprod.desc f g))).mp
    simp only [Category.assoc, image.fac, biprod.inl_desc, biprod.inr_desc, pullback.condition]
  refine IsPushout.mk ⟨w⟩ ⟨?_⟩
  refine PushoutCocone.IsColimit.mk _
    (fun s =>
      have hk : kernel.ι (biprod.desc f g) ≫ biprod.desc s.inl s.inr = 0 := by
        have : kernel.ι (biprod.desc f g) =
          (pullbackIsoKernelOfDesc f g).inv ≫
            (pullbackIsoKernelOfDesc f g).hom ≫ kernel.ι _ := by
          rw [Iso.inv_hom_id_assoc]
        rw [this, Category.assoc, pullbackIsoKernelOfDesc_hom_ι, biprod.lift_desc,
          Preadditive.neg_comp, s.condition, add_neg_cancel, comp_zero]
      (Abelian.coimageIsoImage' (biprod.desc f g)).inv ≫
        cokernel.desc (kernel.ι (biprod.desc f g)) (biprod.desc s.inl s.inr) hk)
    (fun s => by
      rw [Category.assoc, ← Category.assoc (factorThruImage _),
        Abelian.factorThruImage_comp_coimageIsoImage'_inv, cokernel.π_desc, biprod.inl_desc])
    (fun s => by
      rw [Category.assoc, ← Category.assoc (factorThruImage _),
        Abelian.factorThruImage_comp_coimageIsoImage'_inv, cokernel.π_desc, biprod.inr_desc])
    (fun s m h₁ h₂ => by
      apply (cancel_epi (factorThruImage (biprod.desc f g))).mp
      rw [← Category.assoc, Abelian.factorThruImage_comp_coimageIsoImage'_inv, cokernel.π_desc]
      have t := biprod.total (X := A) (Y := B)
      calc factorThruImage (biprod.desc f g) ≫ m
          = (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫
            factorThruImage (biprod.desc f g) ≫ m := by rw [t, Category.id_comp]
        _ = biprod.fst ≫ ((biprod.inl ≫ factorThruImage (biprod.desc f g)) ≫ m) +
            biprod.snd ≫ ((biprod.inr ≫ factorThruImage (biprod.desc f g)) ≫ m) := by
              simp only [Preadditive.add_comp, Category.assoc]
        _ = biprod.fst ≫ s.inl + biprod.snd ≫ s.inr := by rw [h₁, h₂]
        _ = (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫
            biprod.desc s.inl s.inr := by
              simp only [Preadditive.add_comp, Category.assoc, biprod.inl_desc, biprod.inr_desc]
        _ = biprod.desc s.inl s.inr := by rw [t, Category.id_comp])

end

end SecondIsomorphism
