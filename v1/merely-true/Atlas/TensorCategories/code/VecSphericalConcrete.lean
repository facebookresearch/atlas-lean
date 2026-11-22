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

open CategoryTheory MonoidalCategory Module Category

universe u


attribute [-instance] RigidCategory.toRightRigidCategory

set_option maxHeartbeats 800000

noncomputable section

variable (k : Type u) [Field k]

/-- The concrete left quantum trace of a morphism `a : V ⟶ (V*)*` in `FGModuleCat k`,
obtained by composing the coevaluation, whiskering by `a`, and the evaluation. -/
def vecLeftQuantumTrace {V : FGModuleCat.{u} k} (a : V ⟶ (Vᘁ)ᘁ) :
    𝟙_ (FGModuleCat.{u} k) ⟶ 𝟙_ (FGModuleCat.{u} k) :=
  η_ V (Vᘁ) ≫ (a ▷ Vᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ)

/-- The concrete pivotal dimension of `V` in `FGModuleCat k`, defined as the left
quantum trace of the canonical double-dual evaluation iso `V ≅ (V*)*`. -/
def vecPivotalDim (V : FGModuleCat.{u} k) :
    𝟙_ (FGModuleCat.{u} k) ⟶ 𝟙_ (FGModuleCat.{u} k) :=
  vecLeftQuantumTrace k ((Module.evalEquiv k V).toFGModuleCatIso.hom)

/-- Evaluating the concrete pivotal dimension of `V` at `1 ∈ k` yields `dim_k(V)`,
recovering the classical identification of categorical and linear dimensions. -/
lemma vecPivotalDim_apply_one (V : FGModuleCat.{u} k) :
    (vecPivotalDim k V).hom.hom 1 = (Module.finrank k V : k) := by

  simp only [vecPivotalDim, vecLeftQuantumTrace]

  change (contractLeft k (Dual k V))
    (TensorProduct.map ((Module.evalEquiv k V).toFGModuleCatIso.hom.hom.hom) LinearMap.id
      (coevaluation k V 1)) = (Module.finrank k V : k)

  have heval : (Module.evalEquiv k V).toFGModuleCatIso.hom.hom.hom = Dual.eval k V := rfl
  rw [heval, coevaluation_apply_one]

  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, contractLeft_apply,
    Dual.eval_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
    Finset.sum_const, Nat.smul_one_eq_cast]
  congr 1
  rw [Finset.card_univ]
  exact (Module.finrank_eq_card_basis (Basis.ofVectorSpace k V)).symm

/-- The sphericality condition for `FGModuleCat k`: the concrete pivotal dimension
of `V` agrees with that of its dual `V*`, since `dim_k V = dim_k V*`. -/
lemma vec_spherical_condition (V : FGModuleCat.{u} k) :
    vecPivotalDim k V = vecPivotalDim k (Vᘁ) := by


  have h1 : (vecPivotalDim k V).hom.hom 1 = (Module.finrank k V : k) :=
    vecPivotalDim_apply_one k V

  have h2 : (vecPivotalDim k (Vᘁ)).hom.hom 1 = (Module.finrank k (Dual k V) : k) := by
    simp only [vecPivotalDim, vecLeftQuantumTrace]
    change (contractLeft k (Dual k (Dual k V)))
      (TensorProduct.map
        ((Module.evalEquiv k (Dual k V)).toFGModuleCatIso.hom.hom.hom) LinearMap.id
        (coevaluation k (Dual k V) 1)) = (Module.finrank k (Dual k V) : k)
    have heval : (Module.evalEquiv k (Dual k V)).toFGModuleCatIso.hom.hom.hom =
        Dual.eval k (Dual k V) := rfl
    rw [heval, coevaluation_apply_one]
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, contractLeft_apply,
      Dual.eval_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
      Finset.sum_const, Nat.smul_one_eq_cast]
    congr 1
    rw [Finset.card_univ]
    exact (Module.finrank_eq_card_basis (Basis.ofVectorSpace k (Dual k V))).symm

  have h3 : (vecPivotalDim k V).hom.hom 1 = (vecPivotalDim k (Vᘁ)).hom.hom 1 := by
    rw [h1, h2]
    congr 1
    exact (Subspace.dual_finrank_eq (K := k) (V := V)).symm

  exact InducedCategory.Hom.ext (ModuleCat.Hom.ext (LinearMap.ext_ring h3))

end
