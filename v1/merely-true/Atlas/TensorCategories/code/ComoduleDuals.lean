/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.CoalgebraBialgebra
import Atlas.TensorCategories.code.HopfAlgebra
import Mathlib.LinearAlgebra.Contraction

set_option maxHeartbeats 800000

open scoped TensorProduct
open Coalgebra HopfAlgebra LinearMap

universe u v

section RightDualComodule

variable (k : Type u) [CommSemiring k] (H : Type v) [Semiring H] [HopfAlgebra k H]
variable (X : Type v) [AddCommGroup X] [Module k X]
variable [Module.Free k X] [Module.Finite k X]

/-- Uncurried form of the dual coaction map: given a coaction `π : X → X ⊗ H`, produces
the linear map `X* ⊗ X → H` obtained by combining the antipode, the original coaction,
and the evaluation pairing. -/
noncomputable def dualCoactUncurried (π : X →ₗ[k] X ⊗[k] H) :
    Module.Dual k X ⊗[k] X →ₗ[k] H :=
  (TensorProduct.lid k H).toLinearMap ∘ₗ
  (contractLeft k X).rTensor H ∘ₗ
  (TensorProduct.assoc k (Module.Dual k X) X H).symm.toLinearMap ∘ₗ
  ((HopfAlgebra.antipode k : H →ₗ[k] H).lTensor X ∘ₗ π).lTensor (Module.Dual k X)

/-- Curried version of `dualCoactUncurried`: a map `X* → (X → H)`. -/
noncomputable def dualCoactCurried (π : X →ₗ[k] X ⊗[k] H) :
    Module.Dual k X →ₗ[k] (X →ₗ[k] H) :=
  TensorProduct.curry (dualCoactUncurried k H X π)

/-- The dual coaction `X* → X* ⊗ H` on the linear dual of an `H`-comodule, used in
Corollary 1.22.6 to equip `X*` with a right `H`-comodule structure via the antipode. -/
noncomputable def dualCoaction (π : X →ₗ[k] X ⊗[k] H) :
    Module.Dual k X →ₗ[k] Module.Dual k X ⊗[k] H :=
  (dualTensorHomEquiv k X H).symm.toLinearMap ∘ₗ dualCoactCurried k H X π

omit [Module.Free k X] [Module.Finite k X] in
/-- A naturality identity reducing a composite of left-id, contraction, associator inverse,
and `mk` to `lid` composed with `rTensor`. -/
lemma lid_contractLeft_rTensor_assoc_eq_lid_rTensor (f : Module.Dual k X) :
    (TensorProduct.lid k H).toLinearMap ∘ₗ
    (contractLeft k X).rTensor H ∘ₗ
    (TensorProduct.assoc k (Module.Dual k X) X H).symm.toLinearMap ∘ₗ
    (TensorProduct.mk k (Module.Dual k X) (X ⊗[k] H)) f =
    (TensorProduct.lid k H).toLinearMap ∘ₗ f.rTensor H := by
  ext y h
  simp [contractLeft, rTensor_tmul, TensorProduct.assoc_symm_tmul,
        TensorProduct.mk_apply, TensorProduct.lid_tmul]

omit [Module.Free k X] [Module.Finite k X] in
/-- Compatibility of `dualTensorHom` with `lTensor`: postcomposing with `g` on the
target commutes with applying `dualTensorHom`. -/
lemma dualTensorHom_lTensor_comp {N P : Type*} [AddCommMonoid N] [Module k N]
    [AddCommMonoid P] [Module k P]
    (g : N →ₗ[k] P) (t : Module.Dual k X ⊗[k] N) (m : X) :
    (dualTensorHom k X P (g.lTensor (Module.Dual k X) t)) m =
    g ((dualTensorHom k X N t) m) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f n =>
    simp [dualTensorHom_apply, LinearMap.lTensor_tmul, map_smul]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]; rw [hx, hy]

omit [Module.Free k X] [Module.Finite k X] in
/-- Counit compatibility for the curried dual coaction: composing
`Coalgebra.counit` with `dualCoactCurried` returns the original functional `f`. -/
lemma counit_comp_dualCoactCurried (π : X →ₗ[k] X ⊗[k] H)
    (hcounit : Coalgebra.counit.lTensor X ∘ₗ π = (TensorProduct.mk k X k).flip 1)
    (f : Module.Dual k X) :
    Coalgebra.counit ∘ₗ dualCoactCurried k H X π f = f := by
  ext m
  simp only [coe_comp, Function.comp_apply]
  show Coalgebra.counit (dualCoactUncurried k H X π (f ⊗ₜ[k] m)) = f m
  unfold dualCoactUncurried
  simp only [coe_comp, Function.comp_apply, LinearEquiv.coe_coe, lTensor_tmul]

  have hs1 := congr_fun (congr_arg DFunLike.coe
    (lid_contractLeft_rTensor_assoc_eq_lid_rTensor k H X f))
    ((HopfAlgebra.antipode k : H →ₗ[k] H).lTensor X (π m))
  simp only [coe_comp, Function.comp_apply, LinearEquiv.coe_coe, TensorProduct.mk_apply] at hs1
  rw [hs1]

  have hs2 : Coalgebra.counit ∘ₗ (TensorProduct.lid k H).toLinearMap ∘ₗ f.rTensor H =
      (TensorProduct.lid k k).toLinearMap ∘ₗ f.rTensor k ∘ₗ
        (Coalgebra.counit (R := k)).lTensor X := by
    ext y h; simp [rTensor_tmul, TensorProduct.lid_tmul, map_smul]
  have hs2' := congr_fun (congr_arg DFunLike.coe hs2)
    ((HopfAlgebra.antipode k : H →ₗ[k] H).lTensor X (π m))
  simp only [coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hs2'
  rw [hs2']

  have hs3 : (Coalgebra.counit (R := k)).lTensor X
      ((HopfAlgebra.antipode k : H →ₗ[k] H).lTensor X (π m)) =
      (Coalgebra.counit (R := k)).lTensor X (π m) := by
    have : (Coalgebra.counit (R := k)).lTensor X ∘ₗ
        (HopfAlgebra.antipode k : H →ₗ[k] H).lTensor X =
        (Coalgebra.counit (R := k)).lTensor X := by
      ext y h; simp [lTensor_tmul, counit_antipode]
    exact congr_fun (congr_arg DFunLike.coe this) (π m)
  rw [hs3]

  have hs4 : (Coalgebra.counit (R := k)).lTensor X (π m) = m ⊗ₜ[k] (1 : k) :=
    congr_fun (congr_arg DFunLike.coe hcounit) m
  rw [hs4]

  simp [TensorProduct.lid_tmul]


/-- The counit axiom for the dual coaction on `X*`: applying the counit recovers the
canonical embedding of `X*` into `X* ⊗ k`. -/
theorem dualCoaction_counit (hπ : RightComodule k H X) :
    Coalgebra.counit.lTensor (Module.Dual k X) ∘ₗ (dualCoaction k H X hπ.coact) =
    (TensorProduct.mk k (Module.Dual k X) k).flip 1 := by
  ext f
  apply (dualTensorHomEquiv k X k).injective
  ext m
  simp only [coe_comp, Function.comp_apply,
             dualTensorHomEquiv, dualTensorHomEquivOfBasis_apply]

  rw [dualTensorHom_lTensor_comp k X (Coalgebra.counit (R := k)) (dualCoaction k H X hπ.coact f) m]


  show Coalgebra.counit ((dualTensorHom k X H (dualCoaction k H X hπ.coact f)) m) =
       (dualTensorHom k X k (((TensorProduct.mk k (Module.Dual k X) k).flip 1) f)) m
  have lhs_eq : (dualTensorHom k X H (dualCoaction k H X hπ.coact f)) m =
      dualCoactCurried k H X hπ.coact f m := by
    unfold dualCoaction
    simp only [coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [show (dualTensorHom k X H
        ((dualTensorHomEquiv k X H).symm (dualCoactCurried k H X hπ.coact f))) m =
        (dualTensorHomEquiv k X H
        ((dualTensorHomEquiv k X H).symm (dualCoactCurried k H X hπ.coact f))) m from rfl]
    simp [LinearEquiv.apply_symm_apply]
  rw [lhs_eq]

  have := congr_fun (congr_arg DFunLike.coe
    (counit_comp_dualCoactCurried k H X hπ.coact hπ.counit_coact f)) m
  simp only [coe_comp, Function.comp_apply] at this
  rw [this]

  simp [dualTensorHom_apply, LinearMap.flip_apply, TensorProduct.mk_apply]


end RightDualComodule
