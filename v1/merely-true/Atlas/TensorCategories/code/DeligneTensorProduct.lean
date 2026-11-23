/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.DeligneTensorProductDef
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Algebra.Category.ModuleCat.Abelian

set_option maxHeartbeats 400000

noncomputable section

open TensorProduct CategoryTheory ModuleCat

namespace Deligne

variable (k : Type) [CommRing k]

section ModuleAction

variable (A : Type) [Ring A] [Algebra k A]
variable (B : Type) [Ring B] [Algebra k B]
variable (M : Type) [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [SMulCommClass k A M]
variable (N : Type) [AddCommGroup N] [Module k N] [Module B N]
  [IsScalarTower k B N] [SMulCommClass k B N]

/-- The `k`-algebra homomorphism `A →ₐ[k] End_k(M ⊗ N)` defined by letting `a ∈ A` act
on the left tensor factor `M`. -/
def actA : A →ₐ[k] Module.End k (M ⊗[k] N) :=
  (Module.End.rTensorAlgHom k M N).comp (Algebra.lsmul k k M)

/-- The `k`-algebra homomorphism `B →ₐ[k] End_k(M ⊗ N)` defined by letting `b ∈ B` act
on the right tensor factor `N`. -/
def actB : B →ₐ[k] Module.End k (M ⊗[k] N) :=
  (Module.End.lTensorAlgHom k N M).comp (Algebra.lsmul k k N)

/-- The actions of `A` (on the left factor) and `B` (on the right factor) on `M ⊗ N`
commute as endomorphisms of `M ⊗[k] N`. -/
theorem actA_actB_commute (a : A) (b : B) :
    Commute (actA k A M N a) (actB k B M N b) := by
  unfold actA actB
  simp only [AlgHom.comp_apply]
  rw [Commute, SemiconjBy]
  change (((Algebra.lsmul k k M) a).rTensor N).comp
      (((Algebra.lsmul k k N) b).lTensor M) =
    (((Algebra.lsmul k k N) b).lTensor M).comp
      (((Algebra.lsmul k k M) a).rTensor N)
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- The combined `(A ⊗[k] B)`-action on `M ⊗[k] N`, obtained from the commuting
`A`- and `B`-actions via the universal property of the algebra tensor product. -/
def actAB : (A ⊗[k] B) →ₐ[k] Module.End k (M ⊗[k] N) :=
  Algebra.TensorProduct.lift (actA k A M N) (actB k B M N) (actA_actB_commute k A B M N)

/-- Computation rule for the `(A ⊗ B)`-action on `M ⊗ N`: the pure tensor
`(a ⊗ b) • (m ⊗ n)` equals `(a • m) ⊗ (b • n)`. -/
theorem actAB_tmul_tmul (a : A) (b : B) (m : M) (n : N) :
    actAB k A B M N (a ⊗ₜ[k] b) (m ⊗ₜ[k] n) = (a • m) ⊗ₜ[k] (b • n) := by
  unfold actAB
  simp [Algebra.TensorProduct.lift_tmul]
  unfold actA actB
  simp [AlgHom.comp_apply, Module.End.rTensorAlgHom_apply_apply,
        Module.End.lTensorAlgHom_apply_apply]
  simp [liftAux_tmul, Algebra.lsmul_coe, LinearMap.compl₂_apply, mk_apply]

/-- The `(A ⊗[k] B)`-module structure on `M ⊗[k] N` coming from `actAB`. -/
@[reducible]
def tensorModule : Module (A ⊗[k] B) (M ⊗[k] N) :=
  Module.compHom _ (actAB k A B M N).toRingHom

end ModuleAction

section Boxtimes

variable (A : Type) [Ring A] [Algebra k A]
variable (B : Type) [Ring B] [Algebra k B]
variable (M : Type) [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [SMulCommClass k A M]
variable (N : Type) [AddCommGroup N] [Module k N] [Module B N]
  [IsScalarTower k B N] [SMulCommClass k B N]

/-- The Deligne tensor product `M ⊠ N` of an `A`-module `M` and a `B`-module `N`,
realised as the `(A ⊗[k] B)`-module `M ⊗[k] N`. -/
def boxtimes : ModuleCat (A ⊗[k] B) :=
  haveI := tensorModule k A B M N
  ModuleCat.of (A ⊗[k] B) (M ⊗[k] N)

end Boxtimes

section BoxtimesMap

variable (A : Type) [Ring A] [Algebra k A]
variable (B : Type) [Ring B] [Algebra k B]
variable (M₁ : Type) [AddCommGroup M₁] [Module k M₁] [Module A M₁]
  [IsScalarTower k A M₁] [SMulCommClass k A M₁]
variable (N₁ : Type) [AddCommGroup N₁] [Module k N₁] [Module B N₁]
  [IsScalarTower k B N₁] [SMulCommClass k B N₁]
variable (M₂ : Type) [AddCommGroup M₂] [Module k M₂] [Module A M₂]
  [IsScalarTower k A M₂] [SMulCommClass k A M₂]
variable (N₂ : Type) [AddCommGroup N₂] [Module k N₂] [Module B N₂]
  [IsScalarTower k B N₂] [SMulCommClass k B N₂]

/-- The functorial action of `⊠` on morphisms: given `A`-linear `f : M₁ → M₂` and
`B`-linear `g : N₁ → N₂`, the map `f ⊠ g : M₁ ⊗ N₁ → M₂ ⊗ N₂` is `(A ⊗ B)`-linear. -/
def boxtimesMap (f : M₁ →ₗ[A] M₂) (g : N₁ →ₗ[B] N₂) :
    letI := tensorModule k A B M₁ N₁
    letI := tensorModule k A B M₂ N₂
    M₁ ⊗[k] N₁ →ₗ[A ⊗[k] B] M₂ ⊗[k] N₂ := by
  letI := tensorModule k A B M₁ N₁
  letI := tensorModule k A B M₂ N₂
  exact {
    toFun := TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)
    map_add' := map_add _
    map_smul' := by
      intro r x
      show TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)
            (actAB k A B M₁ N₁ r x) =
           actAB k A B M₂ N₂ r
            (TensorProduct.map (f.restrictScalars k) (g.restrictScalars k) x)
      induction r using TensorProduct.induction_on with
      | zero => simp [map_zero]
      | tmul a b =>
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul m n =>
          simp [actAB_tmul_tmul, TensorProduct.map_tmul,
                LinearMap.restrictScalars_apply, f.map_smul, g.map_smul]
        | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
      | add r₁ r₂ hr₁ hr₂ =>
        simp only [map_add, LinearMap.add_apply] at hr₁ hr₂ ⊢; rw [hr₁, hr₂]
  }

/-- Computation rule for `boxtimesMap` on pure tensors: `(f ⊠ g) (m ⊗ n) = f m ⊗ g n`. -/
theorem boxtimesMap_tmul (f : M₁ →ₗ[A] M₂) (g : N₁ →ₗ[B] N₂)
    (m : M₁) (n : N₁) :
    boxtimesMap k A B M₁ N₁ M₂ N₂ f g (m ⊗ₜ[k] n) = (f m) ⊗ₜ[k] (g n) := by
  simp [boxtimesMap, TensorProduct.map_tmul, LinearMap.restrictScalars_apply]

variable (M₃ : Type) [AddCommGroup M₃] [Module k M₃] [Module A M₃]
  [IsScalarTower k A M₃] [SMulCommClass k A M₃]
variable (N₃ : Type) [AddCommGroup N₃] [Module k N₃] [Module B N₃]
  [IsScalarTower k B N₃] [SMulCommClass k B N₃]

end BoxtimesMap

section HomMap

variable (A : Type) [Ring A] [Algebra k A]
variable (B : Type) [Ring B] [Algebra k B]
variable (M₁ N₁ : Type) [AddCommGroup M₁] [Module k M₁] [Module A M₁]
  [IsScalarTower k A M₁]
  [AddCommGroup N₁] [Module k N₁] [Module A N₁]
  [IsScalarTower k A N₁] [SMulCommClass k A N₁]
variable (M₂ N₂ : Type) [AddCommGroup M₂] [Module k M₂] [Module B M₂]
  [IsScalarTower k B M₂]
  [AddCommGroup N₂] [Module k N₂] [Module B N₂]
  [IsScalarTower k B N₂] [SMulCommClass k B N₂]

/-- The `k`-bilinear map `(f, g) ↦ f ⊗ g` from `Hom_A(M₁, N₁) × Hom_B(M₂, N₂)` to
`Hom_k(M₁ ⊗ M₂, N₁ ⊗ N₂)`. -/
def homMapBilinear :
    (M₁ →ₗ[A] N₁) →ₗ[k] (M₂ →ₗ[B] N₂) →ₗ[k]
      (M₁ ⊗[k] M₂ →ₗ[k] N₁ ⊗[k] N₂) :=
  LinearMap.mk₂ k
    (fun f g => TensorProduct.map (f.restrictScalars k) (g.restrictScalars k))
    (by intros; ext m n; simp [TensorProduct.map_tmul, TensorProduct.add_tmul])
    (by intros; ext m n; simp [TensorProduct.map_tmul,
          LinearMap.restrictScalars_smul, TensorProduct.smul_tmul'])
    (by intros; ext m n; simp [TensorProduct.map_tmul, TensorProduct.tmul_add])
    (by intros; ext m n; simp [TensorProduct.map_tmul,
          LinearMap.restrictScalars_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul'])

/-- The natural `k`-linear map `Hom_A(M₁, N₁) ⊗_k Hom_B(M₂, N₂) → Hom_k(M₁ ⊗ M₂, N₁ ⊗ N₂)`
sending a pure tensor of morphisms to the tensor of the underlying linear maps; an
isomorphism for finite-dimensional modules (Proposition 1.46.2(iv)). -/
def homMap :
    (M₁ →ₗ[A] N₁) ⊗[k] (M₂ →ₗ[B] N₂) →ₗ[k]
      (M₁ ⊗[k] M₂ →ₗ[k] N₁ ⊗[k] N₂) :=
  TensorProduct.lift (homMapBilinear k A B M₁ N₁ M₂ N₂)

end HomMap

section Properties

variable (A : Type) [Ring A] [Algebra k A]
variable (B : Type) [Ring B] [Algebra k B]




/-- Proposition 1.46.2(i): the category `ModuleCat (A ⊗[k] B)` is abelian. -/
def prop_1_46_2_i_abelian :
    Abelian (ModuleCat (A ⊗[k] B)) := inferInstance










end Properties

section UniversalProperty

variable (A : Type) [Ring A] [Algebra k A]
variable (B : Type) [Ring B] [Algebra k B]

end UniversalProperty

section Monoidal

variable (A : Type) [Ring A] [Algebra k A]
variable (B : Type) [Ring B] [Algebra k B]

/-- Underlying `k`-linear iso `(M₁ ⊗ N₁) ⊗ (M₂ ⊗ N₂) ≃ (M₁ ⊗ M₂) ⊗ (N₁ ⊗ N₂)` used to
define the monoidal structure on the Deligne tensor product, given by the standard
interchange of tensor factors. -/
def prop_1_46_3_tensor_boxtimes
    (M₁ M₂ : Type) [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
    (N₁ N₂ : Type) [AddCommGroup N₁] [Module k N₁] [AddCommGroup N₂] [Module k N₂] :
    (M₁ ⊗[k] N₁) ⊗[k] (M₂ ⊗[k] N₂) ≃ₗ[k] (M₁ ⊗[k] M₂) ⊗[k] (N₁ ⊗[k] N₂) :=
  TensorProduct.tensorTensorTensorComm k M₁ N₁ M₂ N₂

end Monoidal

end Deligne

end
