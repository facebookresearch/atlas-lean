/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FiniteTensorCategory

open CategoryTheory MonoidalCategory

universe v u v₁ u₁ w

namespace TensorCategories

/-- Any two Frobenius-Perron dimension functions on a category with a Grothendieck fusion
ring agree on every object, so the FP-dimension function is essentially unique. -/
theorem fpDimFunction_unique
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [hGR : HasGrothendieckFusionRing C]
    (d₁ d₂ : FPdimFunction (C := C)) :
    ∀ (X : C), d₁.fpDim X = d₂.fpDim X := by
  letI := hGR.ι_decidableEq
  letI := hGR.ι_fintype
  letI := hGR.ι_nonempty
  letI := hGR.ι_hasPF
  obtain ⟨fpd⟩ := hGR.fusionRing.exists_FPdimData
  intro X
  rw [hGR.fpDimFunction_eq fpd d₁ X, hGR.fpDimFunction_eq fpd d₂ X]

/-- Corollary 1.45.11: If `F : C -> D` is a quasi-tensor functor between tensor categories
with finitely many classes of simple objects, then for any object `X` in `C` we have
`FPdim_D (F X) = FPdim_C X`. -/
theorem corollary_1_45_11
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D] [RigidCategory D]
    [hC : HasGrothendieckFusionRing C]
    [hD : HasGrothendieckFusionRing D]
    (QTF : QuasiTensorFunctor k C D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D)) :
    ∀ (X : C), dD.fpDim (QTF.F.obj X) = dC.fpDim X := by


  let dComp : FPdimFunction (C := C) :=
  { fpDim := fun X => dD.fpDim (QTF.F.obj X)
    fpDim_unit := by
      have hiso : Nonempty (QTF.F.obj (𝟙_ C) ≅ 𝟙_ D) := ⟨QTF.unitIso⟩
      rw [dD.fpDim_iso _ _ hiso, dD.fpDim_unit]
    fpDim_pos := fun X => dD.fpDim_pos (QTF.F.obj X)
    fpDim_tensor := fun X Y => by
      have hiso : Nonempty (QTF.F.obj (X ⊗ Y) ≅ QTF.F.obj X ⊗ QTF.F.obj Y) :=
        ⟨(QTF.J X Y).symm⟩
      rw [dD.fpDim_iso _ _ hiso, dD.fpDim_tensor]
    fpDim_iso := fun X Y hXY => by
      have hFiso : Nonempty (QTF.F.obj X ≅ QTF.F.obj Y) :=
        hXY.map (fun e => QTF.F.mapIso e)
      exact dD.fpDim_iso _ _ hFiso }


  intro X
  exact fpDimFunction_unique dComp dC X

end TensorCategories
