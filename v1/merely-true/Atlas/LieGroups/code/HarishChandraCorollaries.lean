/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.MaximalQuotients
import Atlas.LieGroups.code.KostantTheorem

universe u_hc_bim

noncomputable section



def HomAdEquivariant.postcomp
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {V : Type*} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    {N M : LieBimodule R 𝔤}
    (π : N.carrier →ₗ[R] M.carrier)
    (hπ_left : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (n : N.carrier),
      π (N.leftAction u n) = M.leftAction u (π n))
    (hπ_right : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (n : N.carrier),
      π (N.rightAction u n) = M.rightAction u (π n)) :
    HomAdEquivariant V N →ₗ[R] HomAdEquivariant V M where
  toFun f := ⟨π.comp f.val, by
    intro x v
    simp only [LinearMap.comp_apply]
    rw [f.property x v]
    show π (N.adjointAction x (f.val v)) = M.adjointAction x (π (f.val v))
    simp only [LieBimodule.adjointAction, LinearMap.sub_apply]
    rw [← hπ_left, ← hπ_right, map_sub]⟩
  map_add' f g := by
    ext v
    simp [LinearMap.comp_apply, LinearMap.add_apply]
  map_smul' c f := by
    ext v
    simp [LinearMap.comp_apply, LinearMap.smul_apply]


end
