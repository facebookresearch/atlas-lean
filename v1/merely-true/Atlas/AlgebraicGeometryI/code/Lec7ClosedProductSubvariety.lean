/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Lec7ClosedProductSubvariety

/-- Helper for Lec 7, Lem 16: the tensor product of two surjective
linear maps is surjective. -/
theorem lemma16_tensorProduct_map_surjective {R M N M' N' : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    {f : M →ₗ[R] M'} {g : N →ₗ[R] N'}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (TensorProduct.map f g) :=
  TensorProduct.map_surjective hf hg

/-- Helper for Lec 7, Lem 16: the tensor product of two surjective
algebra homomorphisms is surjective. -/
theorem lemma16_algebra_tensorProduct_map_surjective {R A₁ B₁ A₂ B₂ : Type*}
    [CommSemiring R] [CommSemiring A₁] [CommSemiring B₁]
    [CommSemiring A₂] [CommSemiring B₂]
    [Algebra R A₁] [Algebra R B₁] [Algebra R A₂] [Algebra R B₂]
    (φ : A₁ →ₐ[R] B₁) (ψ : A₂ →ₐ[R] B₂)
    (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ) :
    Function.Surjective (Algebra.TensorProduct.map φ ψ) :=
  TensorProduct.map_surjective hφ hψ

/-- Product of a closed immersion with the identity on the right is a
closed immersion (used in Lec 7, Lem 16). -/
noncomputable instance isClosedImmersion_prod_map_id_right
    {X₁ Y₁ Z : Scheme} (f : X₁ ⟶ Y₁) [IsClosedImmersion f] :
    IsClosedImmersion (Limits.prod.map f (𝟙 Z)) :=
  IsClosedImmersion.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_prod_fst_with_id f Z) ‹_›

/-- Product of the identity on the left with a closed immersion is a
closed immersion (used in Lec 7, Lem 16). -/
noncomputable instance isClosedImmersion_prod_map_id_left
    {X₂ Y₂ Z : Scheme} (g : X₂ ⟶ Y₂) [IsClosedImmersion g] :
    IsClosedImmersion (Limits.prod.map (𝟙 Z) g) := by
  have h_eq : Limits.prod.map (𝟙 Z) g =
    (Limits.prod.braiding Z X₂).hom ≫ Limits.prod.map g (𝟙 Z) ≫
    (Limits.prod.braiding Y₂ Z).hom := by
    apply prod.hom_ext
    all_goals simp [prod.braiding_hom, prod.lift_fst, prod.lift_snd, prod.map_fst,
      prod.map_snd, ← Category.assoc]
  rw [h_eq]
  have : IsClosedImmersion (Limits.prod.map g (𝟙 Z)) :=
    isClosedImmersion_prod_map_id_right g
  exact IsClosedImmersion.comp _ _

/-- Lec 7, Lem 16: the product of two closed immersions
`i₁ : X₁ ↪ Y₁` and `i₂ : X₂ ↪ Y₂` is a closed immersion
`X₁ × X₂ ↪ Y₁ × Y₂`. -/
theorem lemma16_closed_product_subvariety
    {X₁ X₂ Y₁ Y₂ : Scheme} (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] :
    IsClosedImmersion (Limits.prod.map i₁ i₂) := by
  have h_eq : Limits.prod.map i₁ i₂ =
    Limits.prod.map i₁ (𝟙 X₂) ≫ Limits.prod.map (𝟙 Y₁) i₂ := by
    simp [Limits.prod.map_map]
  rw [h_eq]
  exact IsClosedImmersion.comp _ _

end Lec7ClosedProductSubvariety
