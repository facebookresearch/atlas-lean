/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

set_option maxHeartbeats 800000

namespace CategoryTheory

open CategoryTheory MonoidalCategory Limits

/-- Linear equivalence `(X ⊗ Z ⟶ Y) ≃ₗ[k] (X ⟶ Y ⊗ Zᘁ)` upgrading the
right-dual hom adjunction (`tensorRightHomEquiv`) in a `k`-linear rigid
monoidal category. -/
noncomputable def tensorRightHomLinearEquiv (k : Type w) [Field k]
    {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear k C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C]
    (X Z Y : C) :
    (X ⊗ Z ⟶ Y) ≃ₗ[k] (X ⟶ Y ⊗ Zᘁ) :=
  LinearEquiv.ofBijective
    { toFun := (tensorRightHomEquiv X Z (Zᘁ) Y).toFun
      map_add' := fun f g => by
        simp only [tensorRightHomEquiv]
        simp [MonoidalPreadditive.add_whiskerRight]
      map_smul' := fun r f => by
        simp only [tensorRightHomEquiv]
        simp [MonoidalLinear.smul_whiskerRight] }
    ⟨fun f g h => (tensorRightHomEquiv X Z (Zᘁ) Y).injective h,
     fun g => ⟨(tensorRightHomEquiv X Z (Zᘁ) Y).symm g,
       (tensorRightHomEquiv X Z (Zᘁ) Y).apply_symm_apply g⟩⟩

/-- The right-dual hom adjunction is a linear equivalence, hence the
`k`-dimensions agree: `dim (X ⊗ Z ⟶ Y) = dim (X ⟶ Y ⊗ Zᘁ)`. -/
theorem hom_tensor_right_finrank_eq (k : Type w) [Field k]
    {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear k C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C]
    (X Z Y : C) :
    Module.finrank k (X ⊗ Z ⟶ Y) = Module.finrank k (X ⟶ Y ⊗ Zᘁ) :=
  LinearEquiv.finrank_eq (tensorRightHomLinearEquiv k X Z Y)

/-- Bundle of combinatorial data witnessing the finiteness of a multitensor
category `C`: indexed simples and projective covers, structure constants
`N_{ij}^l`, Jordan–Hölder multiplicities, the dual involution, and the
projective-cover multiplicity identities used to formulate the
Frobenius–Perron results of EGNO §1.47. -/
class FiniteMultitensorDecompData (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] where
  I : Type*
  [instFintype : Fintype I]
  [instDecEq : DecidableEq I]
  simpleObj : I → C
  simpleObj_simple : ∀ i, Simple (simpleObj i)
  projCover : I → C
  projCover_projective : ∀ i, Projective (projCover i)
  dualIndex : I → I
  structConst : I → I → I → ℕ
  structConst_eq : ∀ i j l,
    structConst i j l = Module.finrank k (simpleObj i ⊗ simpleObj j ⟶ simpleObj l)
  jhMult : C → I → ℕ
  hom_projCover_eq_mult : ∀ (i : I) (Y : C),
    Module.finrank k (projCover i ⟶ Y) = jhMult Y i
  projDecompMult : C → I → ℕ
  projDecompMult_eq_hom : ∀ (Q : C) [Projective Q] (k' : I),
    projDecompMult Q k' = Module.finrank k (Q ⟶ simpleObj k')
  jhMult_tensor_dual_eq : ∀ (k' i : I) (Z : C),
    jhMult (simpleObj k' ⊗ Zᘁ) i =
      ∑ l : I, structConst k' (dualIndex i) l * jhMult Z l
  jhMult_leftdual_tensor_eq : ∀ (k' i : I) (Z : C),
    jhMult ((ᘁZ) ⊗ simpleObj k') i =
      ∑ l : I, structConst l k' i * jhMult Z l

attribute [reducible, instance] FiniteMultitensorDecompData.instFintype
  FiniteMultitensorDecompData.instDecEq

section Prop1472

variable {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C]
    [d : FiniteMultitensorDecompData k C]

/-- Linear equivalence `(Z ⊗ P ⟶ Y) ≃ₗ[k] (P ⟶ (ᘁZ) ⊗ Y)` upgrading the
left-dual hom adjunction (`tensorLeftHomEquiv`) in a `k`-linear rigid
monoidal category. -/
noncomputable def tensorLeftHomLinearEquiv
    (Z P Y : C) :
    (Z ⊗ P ⟶ Y) ≃ₗ[k] (P ⟶ (ᘁZ) ⊗ Y) :=
  LinearEquiv.ofBijective
    { toFun := (tensorLeftHomEquiv P (ᘁZ) Z Y).toFun
      map_add' := fun f g => by
        simp only [tensorLeftHomEquiv]
        simp [MonoidalPreadditive.whiskerLeft_add]
      map_smul' := fun r f => by
        simp only [tensorLeftHomEquiv]
        simp [MonoidalLinear.whiskerLeft_smul] }
    ⟨fun f g h => (tensorLeftHomEquiv P (ᘁZ) Z Y).injective h,
     fun g => ⟨(tensorLeftHomEquiv P (ᘁZ) Z Y).symm g,
       (tensorLeftHomEquiv P (ᘁZ) Z Y).apply_symm_apply g⟩⟩

omit d in
/-- The left-dual hom adjunction is a linear equivalence, hence the
`k`-dimensions agree: `dim (Z ⊗ P ⟶ Y) = dim (P ⟶ (ᘁZ) ⊗ Y)`. -/
theorem hom_tensor_left_finrank_eq
    (Z P Y : C) :
    Module.finrank k (Z ⊗ P ⟶ Y) = Module.finrank k (P ⟶ (ᘁZ) ⊗ Y) :=
  LinearEquiv.finrank_eq (tensorLeftHomLinearEquiv Z P Y)

/-- Indexed family of projective covers whose biproduct decomposes
`P_i ⊗ Z`, with `k'`-summands repeated `Σ_l N_{k', i*}^l · [Z:X_l]` times
(the multiplicities appearing in Proposition 1.47.2, left version). -/
def projTensorLeftDecompFamily (i : d.I) (Z : C) :
    ((k' : d.I) × Fin (∑ l : d.I, d.structConst k' (d.dualIndex i) l * d.jhMult Z l)) → C :=
  fun p => d.projCover p.1

/-- Indexed family of projective covers whose biproduct decomposes
`Z ⊗ P_i`, with `k'`-summands repeated `Σ_l N_{l, k'}^i · [Z:X_l]` times
(the multiplicities appearing in Proposition 1.47.2, right version). -/
def projTensorRightDecompFamily (i : d.I) (Z : C) :
    ((k' : d.I) × Fin (∑ l : d.I, d.structConst l k' i * d.jhMult Z l)) → C :=
  fun p => d.projCover p.1


end Prop1472

/-- Numerical data of the Frobenius–Perron dimensions of simples and
projective covers in a finite tensor category, together with the
dual involution and the identity `FPdim(P_i)·FPdim(X_{i*}) = FPdim(C)`
from EGNO §1.47. -/
structure FiniteTensorCategoryFPdimData where
  I : Type*
  [instFintype : Fintype I]
  [instDecEq : DecidableEq I]
  [instNonempty : Nonempty I]
  fpDimSimple : I → ℝ
  fpDimProjCover : I → ℝ
  dualIndex : I → I
  fpDimSimple_pos : ∀ i, fpDimSimple i > 0
  fpDimProjCover_pos : ∀ i, fpDimProjCover i > 0
  fpDim_projCover_eq : ∀ i,
    fpDimProjCover i * fpDimSimple (dualIndex i) =
      ∑ j : I, fpDimSimple j * fpDimProjCover j

attribute [instance] FiniteTensorCategoryFPdimData.instFintype
  FiniteTensorCategoryFPdimData.instDecEq
  FiniteTensorCategoryFPdimData.instNonempty

namespace FiniteTensorCategoryFPdimData

variable (D : FiniteTensorCategoryFPdimData)

/-- The Frobenius–Perron dimension of the finite tensor category,
defined as `FPdim(C) := Σ_i FPdim(X_i) · FPdim(P_i)` (EGNO Definition 1.47.5). -/
noncomputable def catFPdim : ℝ :=
  ∑ i : D.I, D.fpDimSimple i * D.fpDimProjCover i

end FiniteTensorCategoryFPdimData

end CategoryTheory
