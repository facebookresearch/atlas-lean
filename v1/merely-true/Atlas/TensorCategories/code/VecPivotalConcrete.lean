/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.TensorCategories.code.PivotalSpherical
import Atlas.TensorCategories.code.VecInstances
import Atlas.TensorCategories.code.VecDualMapBridge

open CategoryTheory MonoidalCategory Module Category TensorCategories

universe u

noncomputable section

variable (k : Type u) [Field k]

section FixDiamond


attribute [-instance] BraidedCategory.rightRigidCategoryOfLeftRigidCategory
attribute [-instance] BraidedCategory.rigidCategoryOfLeftRigidCategory
attribute [-instance] RigidCategory.toRightRigidCategory

/-- The concrete double-dual isomorphism `V ≅ (V*)*` in `FGModuleCat k`, obtained
from the canonical evaluation equivalence on finite-dimensional vector spaces. -/
noncomputable def vecDoubleDualIsoConcrete (V : FGModuleCat k) : V ≅ (Vᘁ)ᘁ :=
  (Module.evalEquiv k V).toFGModuleCatIso

/-- The tensor-coherence isomorphism `(V*)* ⊗ (W*)* ≅ ((V ⊗ W)*)*` in `FGModuleCat k`,
built by combining the double-dual isomorphisms on the factors with the one on the tensor. -/
noncomputable def vecTensorCoherenceIsoConcrete (V W : FGModuleCat k) :
    (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : FGModuleCat k)ᘁ : FGModuleCat k)ᘁ :=
  (MonoidalCategory.tensorIso
    (vecDoubleDualIsoConcrete k V).symm
    (vecDoubleDualIsoConcrete k W).symm) ≪≫
  (vecDoubleDualIsoConcrete k (V ⊗ W))

set_option maxHeartbeats 800000 in
/-- Naturality of the concrete double-dual isomorphism: for any `f : V ⟶ W` in
`FGModuleCat k`, the square involving `f` and the iterated right adjoint mate of `f`
commutes. -/
lemma vecDoubleDualIsoConcrete_naturality {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    f ≫ (vecDoubleDualIsoConcrete k W).hom =
      (vecDoubleDualIsoConcrete k V).hom ≫ (rightAdjointMate (rightAdjointMate f)) := by
  apply InducedCategory.Hom.ext
  apply ModuleCat.Hom.ext
  show (vecDoubleDualIsoConcrete k W).hom.hom.hom ∘ₗ f.hom.hom =
       (rightAdjointMate (rightAdjointMate f)).hom.hom ∘ₗ
         (vecDoubleDualIsoConcrete k V).hom.hom.hom
  have hW : (vecDoubleDualIsoConcrete k W).hom.hom.hom = Module.Dual.eval k W := by
    simp [vecDoubleDualIsoConcrete, LinearEquiv.toFGModuleCatIso_hom]; rfl
  have hV : (vecDoubleDualIsoConcrete k V).hom.hom.hom = Module.Dual.eval k V := by
    simp [vecDoubleDualIsoConcrete, LinearEquiv.toFGModuleCatIso_hom]; rfl
  rw [hW, hV]
  have hram : (rightAdjointMate (rightAdjointMate f)).hom.hom =
      (rightAdjointMate f).hom.hom.dualMap :=
    FGModuleCat.rightAdjointMate_hom_eq_dualMap k (rightAdjointMate f)
  have hram1 : (rightAdjointMate f).hom.hom = f.hom.hom.dualMap :=
    FGModuleCat.rightAdjointMate_hom_eq_dualMap k f
  rw [hram, hram1]
  apply LinearMap.ext; intro v
  apply LinearMap.ext; intro ψ
  rfl

/-- Monoidality of the concrete double-dual isomorphism: it factors the iso
`(V ⊗ W) ≅ ((V ⊗ W)*)*` through the iso `V ≅ (V*)*` tensored with `W ≅ (W*)*`,
followed by the tensor-coherence iso. -/
lemma vecDoubleDualIsoConcrete_monoidality (V W : FGModuleCat.{u} k) :
    (vecDoubleDualIsoConcrete k (V ⊗ W)).hom =
      ((vecDoubleDualIsoConcrete k V).hom ⊗ₘ (vecDoubleDualIsoConcrete k W).hom) ≫
        (vecTensorCoherenceIsoConcrete k V W).hom := by
  simp only [vecTensorCoherenceIsoConcrete, Iso.trans_hom, tensorIso_hom]
  rw [tensorHom_comp_tensorHom_assoc]
  simp [Iso.hom_inv_id]

set_option maxHeartbeats 800000 in
/-- The left quantum trace of the concrete double-dual isomorphism on the unit object
equals the identity of the unit — equivalently, `dim(𝟙) = 1` in `Vec_k`. -/
lemma vecDoubleDualIsoConcrete_dimUnit :
    leftQuantumTrace (FGModuleCat k) (vecDoubleDualIsoConcrete k (𝟙_ (FGModuleCat k))).hom =
    𝟙 (𝟙_ (FGModuleCat k)) := by

  have h1 : (leftQuantumTrace (FGModuleCat k)
      (vecDoubleDualIsoConcrete k (𝟙_ (FGModuleCat k))).hom).hom.hom 1 =
      (Module.finrank k (𝟙_ (FGModuleCat.{u} k)) : k) := by
    change (contractLeft k (Dual k (𝟙_ (FGModuleCat.{u} k))))
      (TensorProduct.map (Dual.eval k (𝟙_ (FGModuleCat.{u} k))) LinearMap.id
        (coevaluation k (𝟙_ (FGModuleCat.{u} k)) 1)) = _
    rw [coevaluation_apply_one]
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, contractLeft_apply,
      Dual.eval_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
      Finset.sum_const, Nat.smul_one_eq_cast]
    congr 1
    rw [Finset.card_univ]
    exact (Module.finrank_eq_card_basis (Basis.ofVectorSpace k (𝟙_ (FGModuleCat.{u} k)))).symm

  have h2 : Module.finrank k ↥(𝟙_ (FGModuleCat.{u} k)) = 1 := Module.finrank_self k
  have h3 : (leftQuantumTrace (FGModuleCat k)
      (vecDoubleDualIsoConcrete k (𝟙_ (FGModuleCat k))).hom).hom.hom 1 = (1 : k) := by
    rw [h1, h2, Nat.cast_one]

  exact InducedCategory.Hom.ext (ModuleCat.Hom.ext (LinearMap.ext_ring h3))

set_option maxHeartbeats 800000 in
/-- `FGModuleCat k` is a pivotal category, with pivotal structure given by the canonical
double-dual evaluation isomorphism. This corresponds to Definitions 1.38.1–1.38.2. -/
@[reducible]
noncomputable def vecPivotalCategoryInstance :
    @PivotalCategory (FGModuleCat k) _ _ _ where
  pivotalIso := vecDoubleDualIsoConcrete k
  tensorCoherenceIso := vecTensorCoherenceIsoConcrete k
  naturality := fun f => vecDoubleDualIsoConcrete_naturality k f
  monoidality := fun V W => vecDoubleDualIsoConcrete_monoidality k V W
  dimUnit := vecDoubleDualIsoConcrete_dimUnit k

end FixDiamond

end
