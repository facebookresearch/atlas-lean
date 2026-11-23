/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Abelian

noncomputable section

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

abbrev SL2R := Matrix.SpecialLinearGroup (Fin 2) ℝ

def sl2R : LieSubalgebra ℝ M2 where
  toSubmodule := (Matrix.traceLinearMap (Fin 2) ℝ ℝ).ker
  lie_mem' := by
    intro x y hx hy
    change (Matrix.traceLinearMap (Fin 2) ℝ ℝ) x = 0 at hx
    change (Matrix.traceLinearMap (Fin 2) ℝ ℝ) y = 0 at hy
    show (Matrix.traceLinearMap (Fin 2) ℝ ℝ) ⁅x, y⁆ = 0
    simp only [Ring.lie_def, map_sub, Matrix.traceLinearMap_apply]
    rw [Matrix.trace_mul_comm]; ring

def basisH : M2 := !![1, 0; 0, -1]

def basisE : M2 := !![0, 1; 0, 0]

def basisF : M2 := !![0, 0; 1, 0]

def sl2C : LieSubalgebra ℂ M2C where
  toSubmodule := (Matrix.traceLinearMap (Fin 2) ℂ ℂ).ker
  lie_mem' := by
    intro x y hx hy
    change (Matrix.traceLinearMap (Fin 2) ℂ ℂ) x = 0 at hx
    change (Matrix.traceLinearMap (Fin 2) ℂ ℂ) y = 0 at hy
    show (Matrix.traceLinearMap (Fin 2) ℂ ℂ) ⁅x, y⁆ = 0
    simp only [Ring.lie_def, map_sub, Matrix.traceLinearMap_apply]
    rw [Matrix.trace_mul_comm]; ring

def basisH_C : M2C := !![1, 0; 0, -1]

def basisE_C : M2C := !![0, 1; 0, 0]

def basisF_C : M2C := !![0, 0; 1, 0]

theorem lie_H_E_C : ⁅basisH_C, basisE_C⁆ = 2 • basisE_C := by
  simp only [Ring.lie_def, basisH_C, basisE_C]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]; ring

theorem lie_H_F_C : ⁅basisH_C, basisF_C⁆ = (-2) • basisF_C := by
  simp only [Ring.lie_def, basisH_C, basisF_C]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]; ring

theorem lie_E_F_C : ⁅basisE_C, basisF_C⁆ = basisH_C := by
  simp only [Ring.lie_def, basisE_C, basisF_C, basisH_C]
  ext i j; fin_cases i <;> fin_cases j <;> simp

def SO2 : Subgroup SL2R where
  carrier := {A | (↑A : M2).transpose * ↑A = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_mul] at *
    rw [Matrix.transpose_mul]
    have : (↑b : M2).transpose * (↑a : M2).transpose * ((↑a : M2) * (↑b : M2)) =
           (↑b : M2).transpose * ((↑a : M2).transpose * (↑a : M2)) * (↑b : M2) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [this, ha, Matrix.mul_one, hb]
  one_mem' := by
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_one,
               Matrix.transpose_one, Matrix.mul_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    set A : M2 := ↑a with hA
    have hdet : A.det = 1 := a.2
    have hAdj : (↑(a⁻¹) : M2) = A.adjugate := Matrix.SpecialLinearGroup.coe_inv a
    rw [hAdj]
    have htrans_eq : A.transpose = A.adjugate := by
      have h1 : A * A.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
      calc A.transpose
          = A.transpose * (A * A.adjugate) := by rw [h1, Matrix.mul_one]
        _ = (A.transpose * A) * A.adjugate := by rw [Matrix.mul_assoc]
        _ = 1 * A.adjugate := by rw [ha]
        _ = A.adjugate := by rw [Matrix.one_mul]
    rw [← htrans_eq, Matrix.transpose_transpose, htrans_eq,
        Matrix.mul_adjugate, hdet, one_smul]

def IwasawaA : Subgroup SL2R where
  carrier := {A | ∃ a : ℝ, 0 < a ∧ (↑A : M2) = !![a, 0; 0, a⁻¹]}
  mul_mem' := by
    intro x y ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
    refine ⟨a * b, mul_pos ha hb, ?_⟩
    simp only [Matrix.SpecialLinearGroup.coe_mul, hxa, hyb]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  one_mem' := by
    refine ⟨1, one_pos, ?_⟩
    simp [Matrix.SpecialLinearGroup.coe_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_mem' := by
    intro x ⟨a, ha, hxa⟩
    refine ⟨a⁻¹, inv_pos.mpr ha, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_inv, hxa]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.adjugate_fin_two, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one]

def IwasawaN : Subgroup SL2R where
  carrier := {A | ∃ x : ℝ, (↑A : M2) = !![1, x; 0, 1]}
  mul_mem' := by
    intro a b ⟨x, hxa⟩ ⟨y, hyb⟩
    refine ⟨x + y, ?_⟩
    simp only [Matrix.SpecialLinearGroup.coe_mul, hxa, hyb]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  one_mem' := by
    refine ⟨0, ?_⟩
    simp [Matrix.SpecialLinearGroup.coe_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_mem' := by
    intro a ⟨x, hxa⟩
    refine ⟨-x, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_inv, hxa]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.adjugate_fin_two, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one]

def lieAlgK : Submodule ℝ M2 where
  carrier := {X | X.transpose = -X ∧ X.trace = 0}
  add_mem' := by
    intro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨by rw [Matrix.transpose_add, ha1, hb1, neg_add],
           by rw [Matrix.trace_add, ha2, hb2, add_zero]⟩
  zero_mem' := ⟨by simp, Matrix.trace_zero (Fin 2) ℝ⟩
  smul_mem' := by
    intro c a ⟨ha1, ha2⟩
    exact ⟨by rw [Matrix.transpose_smul, ha1, smul_neg],
           by rw [Matrix.trace_smul, ha2, smul_zero]⟩

def lieAlgP : Submodule ℝ M2 where
  carrier := {X | X.transpose = X ∧ X.trace = 0}
  add_mem' := by
    intro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨by rw [Matrix.transpose_add, ha1, hb1],
           by rw [Matrix.trace_add, ha2, hb2, add_zero]⟩
  zero_mem' := ⟨Matrix.transpose_zero, Matrix.trace_zero (Fin 2) ℝ⟩
  smul_mem' := by
    intro c a ⟨ha1, ha2⟩
    exact ⟨by rw [Matrix.transpose_smul, ha1],
           by rw [Matrix.trace_smul, ha2, smul_zero]⟩

open Module Fintype in
theorem finrank_sl2C : Module.finrank ℂ sl2C = 3 := by
  suffices h : Module.finrank ℂ (LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ)) = 3 from h
  have h_surj : Function.Surjective (Matrix.traceLinearMap (Fin 2) ℂ ℂ) := by
    intro c
    exact ⟨Matrix.diagonal (fun i => if i = 0 then c else 0), by
      simp [Matrix.traceLinearMap, Matrix.trace, Matrix.diag]⟩
  have key := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
  rw [LinearMap.range_eq_top.mpr h_surj, finrank_top, Module.finrank_matrix] at key
  simp [Fintype.card_fin, finrank_self] at key
  omega

open Module Fintype in
theorem finrank_sl2R : Module.finrank ℝ sl2R = 3 := by
  suffices h : Module.finrank ℝ (LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℝ ℝ)) = 3 from h
  have h_surj : Function.Surjective (Matrix.traceLinearMap (Fin 2) ℝ ℝ) := by
    intro c
    exact ⟨Matrix.diagonal (fun i => if i = 0 then c else 0), by
      simp [Matrix.traceLinearMap, Matrix.trace, Matrix.diag]⟩
  have key := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin 2) ℝ ℝ)
  rw [LinearMap.range_eq_top.mpr h_surj, finrank_top, Module.finrank_matrix] at key
  simp [Fintype.card_fin, finrank_self] at key
  omega

instance sl2C_finiteDimensional : FiniteDimensional ℂ sl2C := by
  have := finrank_sl2C
  exact Module.finite_of_finrank_pos (by omega)

instance sl2R_finiteDimensional : FiniteDimensional ℝ sl2R := by
  have := finrank_sl2R
  exact Module.finite_of_finrank_pos (by omega)

instance sl2C_free : Module.Free ℂ sl2C := Module.Free.of_divisionRing ..

instance sl2R_free : Module.Free ℝ sl2R := Module.Free.of_divisionRing ..

lemma basisH_C_mem_sl2C : basisH_C ∈ sl2C := by
  show (Matrix.traceLinearMap (Fin 2) ℂ ℂ) basisH_C = 0
  simp [basisH_C, Matrix.traceLinearMap, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

lemma basisE_C_mem_sl2C : basisE_C ∈ sl2C := by
  show (Matrix.traceLinearMap (Fin 2) ℂ ℂ) basisE_C = 0
  simp [basisE_C, Matrix.traceLinearMap, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

lemma basisF_C_mem_sl2C : basisF_C ∈ sl2C := by
  show (Matrix.traceLinearMap (Fin 2) ℂ ℂ) basisF_C = 0
  simp [basisF_C, Matrix.traceLinearMap, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

def sl2H : ↥sl2C := ⟨basisH_C, basisH_C_mem_sl2C⟩

def sl2E : ↥sl2C := ⟨basisE_C, basisE_C_mem_sl2C⟩

def sl2F : ↥sl2C := ⟨basisF_C, basisF_C_mem_sl2C⟩

lemma basisH_C_ne_zero : basisH_C ≠ 0 := by
  intro h
  have : basisH_C 0 0 = (0 : M2C) 0 0 := congr_fun (congr_fun h 0) 0
  simp [basisH_C] at this

lemma sl2H_ne_zero : sl2H ≠ 0 := by
  intro h
  have : sl2H.val = 0 := congr_arg Subtype.val h
  exact basisH_C_ne_zero this

lemma sl2_lie_EF : ⁅sl2E, sl2F⁆ = sl2H := by
  apply Subtype.ext
  show ⁅basisE_C, basisF_C⁆ = basisH_C
  exact lie_E_F_C

lemma sl2_lie_HE : ⁅sl2H, sl2E⁆ = 2 • sl2E := by
  apply Subtype.ext
  show ⁅basisH_C, basisE_C⁆ = 2 • basisE_C
  exact lie_H_E_C

lemma sl2_lie_HF : ⁅sl2H, sl2F⁆ = -(2 • sl2F) := by
  apply Subtype.ext
  show ⁅basisH_C, basisF_C⁆ = -(2 • basisF_C)
  rw [lie_H_F_C]; simp

def sl2_isSl2Triple : IsSl2Triple sl2H sl2E sl2F where
  h_ne_zero := sl2H_ne_zero
  lie_e_f := sl2_lie_EF
  lie_h_e_nsmul := sl2_lie_HE
  lie_h_f_nsmul := sl2_lie_HF

end
