/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.TensorCategories.code.VecInstances

open CategoryTheory MonoidalCategory Module

universe u

noncomputable section

variable (k : Type u) [Field k]

set_option maxHeartbeats 800000 in
/-- The right adjoint mate of a morphism `f : V ⟶ W` in `FGModuleCat k` coincides
with the linear dual map `f.dualMap` between the dual spaces. -/
lemma FGModuleCat.rightAdjointMate_hom_eq_dualMap {V W : FGModuleCat.{u} k}
    (f : V ⟶ W) :
    (rightAdjointMate f).hom.hom = f.hom.hom.dualMap := by
  apply LinearMap.ext; intro φ
  apply LinearMap.ext; intro v


  have key := rightAdjointMate_comp_evaluation f

  have key_eval := congrArg (fun g => g.hom.hom (φ ⊗ₜ[k] v)) key
  simp only [] at key_eval

  change (ε_ V Vᘁ).hom.hom (((rightAdjointMate f) ▷ V).hom.hom (φ ⊗ₜ[k] v)) =
         (ε_ W Wᘁ).hom.hom ((Wᘁ ◁ f).hom.hom (φ ⊗ₜ[k] v)) at key_eval

  rw [show ((rightAdjointMate f) ▷ V).hom.hom (φ ⊗ₜ[k] v) =
      (rightAdjointMate f).hom.hom φ ⊗ₜ[k] v from
      ModuleCat.MonoidalCategory.whiskerRight_apply _ _ φ v] at key_eval

  rw [show (Wᘁ ◁ f).hom.hom (φ ⊗ₜ[k] v) =
      φ ⊗ₜ[k] f.hom.hom v from
      ModuleCat.MonoidalCategory.whiskerLeft_apply _ _ φ v] at key_eval

  change (contractLeft k V) ((rightAdjointMate f).hom.hom φ ⊗ₜ[k] v) =
         (contractLeft k W) (φ ⊗ₜ[k] f.hom.hom v) at key_eval
  rw [contractLeft_apply, contractLeft_apply] at key_eval

  exact key_eval

end
