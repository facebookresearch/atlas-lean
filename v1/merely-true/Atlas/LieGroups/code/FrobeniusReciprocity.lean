/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.VermaModules

noncomputable section

universe u

variable {R : Type u} [CommRing R]
variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {Δ : TriangularDecomposition R 𝔤}

def nPosInvariants
    (Δ : TriangularDecomposition R 𝔤)
    (W : Type u) [AddCommGroup W] [Module R W]
    [LieRingModule 𝔤 W] [LieModule R 𝔤 W] : Submodule R W where
  carrier := {w : W | ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), w⁆ = 0}
  add_mem' {a b} ha hb e := by rw [lie_add, ha e, hb e, add_zero]
  zero_mem' e := by rw [lie_zero]
  smul_mem' c _ hm e := by rw [LieModule.lie_smul, hm e, smul_zero]

def singularVectorsOfWeight
    (Δ : TriangularDecomposition R 𝔤)
    (W : Type u) [AddCommGroup W] [Module R W]
    [LieRingModule 𝔤 W] [LieModule R 𝔤 W]
    (wt : Δ.𝔥 →ₗ[R] R) : Submodule R W where
  carrier := {w : W | (∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = wt h • w) ∧
                       (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), w⁆ = 0)}
  add_mem' {a b} ha hb := by
    constructor
    · intro h
      rw [lie_add, ha.1 h, hb.1 h, smul_add]
    · intro e
      rw [lie_add, ha.2 e, hb.2 e, add_zero]
  zero_mem' := by
    constructor
    · intro h; rw [lie_zero, smul_zero]
    · intro e; rw [lie_zero]
  smul_mem' c _ hm := by
    constructor
    · intro h; rw [LieModule.lie_smul, hm.1 h, smul_comm]
    · intro e; rw [LieModule.lie_smul, hm.2 e, smul_zero]

def verma_hom_forward
    {M : Type u} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hV : IsVermaModule Δ M wt)
    {W : Type u} [AddCommGroup W] [Module R W]
    [LieRingModule 𝔤 W] [LieModule R 𝔤 W]
    (φ : M →ₗ⁅R, 𝔤⁆ W) : singularVectorsOfWeight Δ W wt :=
  ⟨φ hV.highestWeightVec, by
    constructor
    · intro h
      have := φ.map_lie (h : 𝔤) hV.highestWeightVec
      rw [hV.cartan_action h, map_smul] at this
      exact this.symm
    · intro e
      have := φ.map_lie (e : 𝔤) hV.highestWeightVec
      rw [hV.npos_action e, map_zero] at this
      exact this.symm⟩

def verma_hom_backward
    {M : Type u} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hV : IsVermaModule Δ M wt)
    {W : Type u} [AddCommGroup W] [Module R W]
    [LieRingModule 𝔤 W] [LieModule R 𝔤 W]
    (w : singularVectorsOfWeight Δ W wt) : M →ₗ⁅R, 𝔤⁆ W :=
  (hV.universal_map W w.val w.prop.1 w.prop.2).choose

lemma verma_hom_backward_spec
    {M : Type u} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hV : IsVermaModule Δ M wt)
    {W : Type u} [AddCommGroup W] [Module R W]
    [LieRingModule 𝔤 W] [LieModule R 𝔤 W]
    (w : singularVectorsOfWeight Δ W wt) :
    (verma_hom_backward hV w) hV.highestWeightVec = w.val :=
  (hV.universal_map W w.val w.prop.1 w.prop.2).choose_spec

theorem verma_hom_forward_backward
    {M : Type u} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hV : IsVermaModule Δ M wt)
    {W : Type u} [AddCommGroup W] [Module R W]
    [LieRingModule 𝔤 W] [LieModule R 𝔤 W]
    (w : singularVectorsOfWeight Δ W wt) :
    verma_hom_forward hV (verma_hom_backward hV w) = w := by
  ext
  exact verma_hom_backward_spec hV w

end
