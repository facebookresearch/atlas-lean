/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FiniteTensorCategory
import Atlas.TensorCategories.code.GrothendieckRingCategorical

open CategoryTheory MonoidalCategory Finset

universe v u

namespace CategoryTheory

/-- Typeclass packaging Jordan-Hölder multiplicities for a rigid linear monoidal abelian
category `C` with categorical fusion data: each object is assigned multiplicities
indexed by the simples in a way compatible with the unit, tensor product and isomorphisms. -/
class HasJordanHolderMultiplicities
    (κ : Type*) [Field κ] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear κ C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
    [RigidCategory C]
    [cfd : CategoricalFusionData κ C] where
  mult : C → cfd.ι → ℕ
  mult_simple : ∀ i j, mult (cfd.S i) j = if i = j then 1 else 0
  mult_unit : ∀ j, mult (𝟙_ C) j = if j = cfd.unitIdx then 1 else 0
  mult_tensor : ∀ (X Y : C) (l : cfd.ι),
    mult (X ⊗ Y) l = ∑ i : cfd.ι, ∑ j : cfd.ι, mult X i * mult Y j * cfd.N i j l
  mult_iso : ∀ (X Y : C), Nonempty (X ≅ Y) → ∀ i, mult X i = mult Y i
  mult_nontrivial : ∀ (X : C), ∃ i, 0 < mult X i

/-- Any `CategoricalFusionData` directly supplies Jordan-Hölder multiplicities by reading off
its built-in multiplicity function and the associated axioms. -/
instance hasJordanHolderMultiplicities_of_categoricalFusionData
    (κ : Type*) [Field κ] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear κ C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
    [RigidCategory C]
    [cfd : CategoricalFusionData κ C] :
    HasJordanHolderMultiplicities κ C where
  mult := cfd.mult
  mult_simple := cfd.mult_simple
  mult_unit := cfd.mult_unit
  mult_tensor := cfd.mult_tensor
  mult_iso := cfd.mult_iso
  mult_nontrivial := cfd.mult_nontrivial

section JHLift

variable {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear κ C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
  [RigidCategory C]
  [cfd : CategoricalFusionData κ C]
  [jh : HasJordanHolderMultiplicities κ C]

/-- Lifts a Frobenius-Perron dimension defined on simples to all objects of `C` by
summing multiplicities weighted by `fpd.d`. -/
noncomputable def jhFpDim
    (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData)
    (X : C) : ℝ :=
  ∑ i : cfd.ι, (jh.mult X i : ℝ) * fpd.d i

/-- The lifted Frobenius-Perron dimension of the unit object equals `1`. -/
theorem jhFpDim_unit
    (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData) :
    jhFpDim fpd (𝟙_ C) = 1 := by
  simp only [jhFpDim, jh.mult_unit]

  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ cfd.unitIdx (fun i => fpd.d i)]
  simp only [Finset.mem_univ, ite_true]
  exact fpd.d_unit

/-- The lifted Frobenius-Perron dimension is strictly positive on every object. -/
theorem jhFpDim_pos
    (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData)
    (X : C) : jhFpDim fpd X > 0 := by
  simp only [jhFpDim]
  obtain ⟨i₀, hi₀⟩ := jh.mult_nontrivial X
  exact lt_of_lt_of_le
    (mul_pos (Nat.cast_pos.mpr hi₀) (fpd.d_pos i₀))
    (Finset.single_le_sum
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) (le_of_lt (fpd.d_pos i)))
      (Finset.mem_univ i₀))

/-- The lifted Frobenius-Perron dimension is multiplicative on tensor products. -/
theorem jhFpDim_tensor
    (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData)
    (X Y : C) : jhFpDim fpd (X ⊗ Y) = jhFpDim fpd X * jhFpDim fpd Y := by
  simp only [jhFpDim, jh.mult_tensor X Y]


  rw [Finset.sum_mul]


  have key : ∀ l : cfd.ι,
    (↑(∑ i : cfd.ι, ∑ j : cfd.ι, jh.mult X i * jh.mult Y j * cfd.N i j l) : ℝ) * fpd.d l =
    ∑ i : cfd.ι, ∑ j : cfd.ι, (jh.mult X i : ℝ) * (jh.mult Y j : ℝ) * (cfd.N i j l : ℝ) * fpd.d l := by
    intro l; push_cast; rw [Finset.sum_mul]; congr 1; ext i
    rw [Finset.sum_mul]
  simp_rw [key]; clear key

  conv_rhs =>
    arg 2; ext i
    rw [mul_comm, Finset.sum_mul]
    arg 2; ext j
    rw [show (jh.mult Y j : ℝ) * fpd.d j * ((jh.mult X i : ℝ) * fpd.d i) =
        (jh.mult X i : ℝ) * (jh.mult Y j : ℝ) * (fpd.d i * fpd.d j) by ring]
    rw [fpd.d_mul i j, Finset.mul_sum]


  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  congr 1; ext i
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  congr 1; ext j
  congr 1; ext k
  simp [CategoricalFusionData.toFusionRing]; ring

/-- The lifted Frobenius-Perron dimension is invariant under isomorphism. -/
theorem jhFpDim_iso
    (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData)
    (X Y : C) (h : Nonempty (X ≅ Y)) : jhFpDim fpd X = jhFpDim fpd Y := by
  simp only [jhFpDim]
  congr 1; ext i
  congr 1
  exact_mod_cast jh.mult_iso X Y h i

/-- Packages the lifted Jordan-Hölder Frobenius-Perron dimension as an `FPdimFunction` on `C`. -/
noncomputable def jhLiftFPdimData
    (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData) :
    FPdimFunction (C := C) where
  fpDim := jhFpDim fpd
  fpDim_unit := jhFpDim_unit fpd
  fpDim_pos := jhFpDim_pos fpd
  fpDim_tensor := jhFpDim_tensor fpd
  fpDim_iso := jhFpDim_iso fpd

end JHLift


section Rank1

/-- The trivial rank-one fusion ring with index set `Fin 1` and the single basis element
acting as the unit. -/
def rank1FusionRing : FusionRing (Fin 1) where
  unit := 0
  N := fun _ _ _ => 1
  star := id
  star_star := fun _ => rfl
  unit_mul := fun j k => by
    have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
    have hk : k = (0 : Fin 1) := Subsingleton.elim k 0
    subst hj; subst hk; simp
  mul_unit := fun i k => by
    have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
    have hk : k = (0 : Fin 1) := Subsingleton.elim k 0
    subst hi; subst hk; simp
  duality := fun i j => by
    have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
    have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
    subst hi; subst hj; simp
  assoc := fun _ _ _ _ => by simp
  N_star_transpose := fun _ _ _ => rfl

/-- The rank-one fusion ring trivially has the Perron-Frobenius property since all
matrices and eigenvectors are one-by-one. -/
instance : FusionRing.HasPerronFrobeniusProperty (Fin 1) where
  pfEigenvec := fun M hM => by
    refine ⟨M 0 0, fun _ => 1, hM 0 0, fun _ => one_pos, ?_⟩
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_one]
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp
  pfUnique := fun M _ r₁ r₂ v w hv hv_eig hw hw_eig => by
    refine ⟨w 0 / v 0, fun i => ?_⟩
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [div_mul_cancel₀]
    exact ne_of_gt (hv 0)


end Rank1

end CategoryTheory
