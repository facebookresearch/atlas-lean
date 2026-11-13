/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Atlas.TensorCategories.code.PerronFrobeniusProof

set_option maxHeartbeats 400000

structure FusionRing (ι : Type*) [DecidableEq ι] [Fintype ι] where
  unit : ι
  N : ι → ι → ι → ℕ
  star : ι → ι
  star_star : ∀ i, star (star i) = i
  unit_mul : ∀ j k, N unit j k = if j = k then 1 else 0
  mul_unit : ∀ i k, N i unit k = if i = k then 1 else 0
  duality : ∀ i j, N i j unit = if j = star i then 1 else 0
  assoc : ∀ i j k l, ∑ m : ι, N i j m * N m k l = ∑ m : ι, N j k m * N i m l
  N_star_transpose : ∀ i j k, N i j k = N (star i) k j

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

section Basic

variable (R : FusionRing ι)

theorem star_injective : Function.Injective R.star := by
  intro a b hab
  have : R.star (R.star a) = R.star (R.star b) := congrArg R.star hab
  rwa [R.star_star, R.star_star] at this

theorem star_surjective : Function.Surjective R.star :=
  fun b => ⟨R.star b, R.star_star b⟩

theorem star_bijective : Function.Bijective R.star :=
  ⟨R.star_injective, R.star_surjective⟩

theorem star_unit : R.star R.unit = R.unit := by
  by_contra h
  have h1 := R.duality R.unit R.unit
  rw [R.unit_mul] at h1
  simp at h1
  exact h h1.symm

end Basic

section AntiAutomorphism

variable (R : FusionRing ι)

def IsAntiAutomorphism (ψ : ι → ι) : Prop :=
  Function.Bijective ψ ∧
  ∀ i j k, R.N (ψ i) j k = R.N i k j

theorem star_isAntiAutomorphism : R.IsAntiAutomorphism R.star := by
  refine ⟨R.star_bijective, fun i j k => ?_⟩


  have h := R.N_star_transpose (R.star i) j k
  rwa [R.star_star] at h

end AntiAutomorphism

section Transitivity

variable (R : FusionRing ι)

def IsTransitive : Prop :=
  (∀ X Z : ι, ∃ Y : ι, 0 < R.N X Y Z) ∧
  (∀ X Z : ι, ∃ Y : ι, 0 < R.N Y X Z)

end Transitivity

section MulMatrix

variable (R : FusionRing ι)

def mulMatrix (i : ι) : Matrix ι ι ℕ :=
  Matrix.of (fun j k => R.N i j k)

@[simp]
theorem mulMatrix_apply (i j k : ι) : R.mulMatrix i j k = R.N i j k := rfl

end MulMatrix

def IsComplexEigenvalue (M : Matrix ι ι ℝ) (μ : ℂ) : Prop :=
  ∃ v : ι → ℂ, v ≠ 0 ∧
    (M.map (↑· : ℝ → ℂ)).mulVec v = μ • v

open Finset BigOperators in
theorem perron_frobenius_spectral_dominance
    {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (ev : ℝ) (evec : ι → ℝ) (hv : ∀ i, 0 < evec i)
    (hev : M.mulVec evec = ev • evec) :
    ∀ μ : ℂ, IsComplexEigenvalue M μ → ‖μ‖ ≤ ev := by
  intro μ ⟨y, hy_ne, hy_eig⟩
  set M_ℂ := M.map (↑· : ℝ → ℂ) with hM_ℂ_def

  set c := Finset.sup' Finset.univ ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
    (fun j => ‖y j‖ / evec j) with hc_def

  have hc_pos : 0 < c := by
    rw [Function.ne_iff] at hy_ne
    obtain ⟨j₀, hj₀⟩ := hy_ne
    calc 0 < ‖y j₀‖ / evec j₀ := div_pos (norm_pos_iff.mpr hj₀) (hv j₀)
      _ ≤ c := Finset.le_sup' (fun j => ‖y j‖ / evec j) (Finset.mem_univ j₀)

  have hyc : ∀ k, ‖y k‖ ≤ c * evec k := by
    intro k
    have h1 : ‖y k‖ / evec k ≤ c :=
      Finset.le_sup' (fun j => ‖y j‖ / evec j) (Finset.mem_univ k)
    rwa [div_le_iff₀ (hv k)] at h1

  have hj_bound : ∀ j, ‖μ‖ * ‖y j‖ ≤ c * ev * evec j := by
    intro j

    have step1 : ‖μ‖ * ‖y j‖ = ‖(M_ℂ.mulVec y) j‖ := by
      rw [← norm_mul]; congr 1
      have := congr_fun hy_eig j; simp [Pi.smul_apply] at this; exact this.symm

    have step2 : ‖(M_ℂ.mulVec y) j‖ ≤ ∑ k, M j k * ‖y k‖ := by
      calc ‖(M_ℂ.mulVec y) j‖ ≤ ∑ k, ‖M_ℂ j k * y k‖ := by
              simp only [Matrix.mulVec, dotProduct]; exact norm_sum_le _ _
        _ = ∑ k, M j k * ‖y k‖ := by
              congr 1; ext k
              rw [norm_mul, show ‖M_ℂ j k‖ = M j k from by
                simp only [M_ℂ, Matrix.map_apply]
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hM j k)]]

    have step3 : ∑ k, M j k * ‖y k‖ ≤ ∑ k, M j k * (c * evec k) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hyc k) (hM j k)

    have step4 : ∑ k, M j k * (c * evec k) = c * ev * evec j := by
      have hevj : ∑ k, M j k * evec k = ev * evec j := by
        have := congr_fun hev j
        simp [Matrix.mulVec, dotProduct, Pi.smul_apply] at this; exact this
      calc ∑ k, M j k * (c * evec k) = c * ∑ k, M j k * evec k := by
              rw [Finset.mul_sum]; congr 1; ext k; ring
        _ = c * (ev * evec j) := by rw [hevj]
        _ = c * ev * evec j := by ring
    linarith [step1, step2, step3, step4]

  obtain ⟨j₀, _, hj₀_eq⟩ := Finset.exists_mem_eq_sup'
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩ (fun j => ‖y j‖ / evec j)
  have hc_eq : c = ‖y j₀‖ / evec j₀ := hj₀_eq
  have hceq : c * evec j₀ = ‖y j₀‖ := by
    rw [hc_eq]; exact div_mul_cancel₀ _ (ne_of_gt (hv j₀))
  have hy_pos : 0 < ‖y j₀‖ := by rw [← hceq]; exact mul_pos hc_pos (hv j₀)

  have h1 := hj_bound j₀
  rw [show c * ev * evec j₀ = ev * (c * evec j₀) from by ring, hceq] at h1
  exact le_of_mul_le_mul_right h1 hy_pos

section FPdim

variable (R : FusionRing ι)

structure FPdimData where
  d : ι → ℝ
  d_unit : d R.unit = 1
  d_pos : ∀ i, d i > 0
  d_mul : ∀ i j, d i * d j = ∑ k : ι, (R.N i j k : ℝ) * d k

structure PerronFrobenius (M : Matrix ι ι ℝ) where
  ev : ℝ
  evec : ι → ℝ
  ev_pos : 0 < ev
  evec_pos : ∀ i, 0 < evec i
  is_eigenvec : M.mulVec evec = ev • evec
  unique : ∀ (μ : ℝ) (w : ι → ℝ), (∀ i, 0 < w i) →
    M.mulVec w = μ • w →
    ∃ c : ℝ, ∀ i, w i = c * evec i

class HasPerronFrobeniusProperty (ι : Type*) [DecidableEq ι] [Fintype ι] [Nonempty ι] where
  pfEigenvec : ∀ (M : Matrix ι ι ℝ), (∀ i j, 0 < M i j) →
    Σ' (r : ℝ) (v : ι → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ M.mulVec v = r • v
  pfUnique : ∀ (M : Matrix ι ι ℝ), (∀ i j, 0 < M i j) →
    ∀ (r₁ r₂ : ℝ) (v w : ι → ℝ),
    (∀ i, 0 < v i) → M.mulVec v = r₁ • v →
    (∀ i, 0 < w i) → M.mulVec w = r₂ • w →
    ∃ c : ℝ, ∀ i, w i = c * v i

noncomputable def perron_frobenius_pos_matrix
    [Nonempty ι] [HasPerronFrobeniusProperty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    PerronFrobenius M :=
  let ⟨r, v, hr_pos, hv_pos, hv_eig⟩ := HasPerronFrobeniusProperty.pfEigenvec M hM
  { ev := r
    evec := v
    ev_pos := hr_pos
    evec_pos := hv_pos
    is_eigenvec := hv_eig
    unique := fun μ w hw_pos hw_eig =>
      HasPerronFrobeniusProperty.pfUnique M hM r μ v w hv_pos hv_eig hw_pos hw_eig }

noncomputable def rightMulMatrix : Matrix ι ι ℝ :=
  Matrix.of (fun j k => (∑ i : ι, R.N j i k : ℝ))

noncomputable def leftMulMatrixR (X : ι) : Matrix ι ι ℝ :=
  Matrix.of (fun j k => (R.N X j k : ℝ))

def leftMulMatrixZ (X : ι) : Matrix ι ι ℤ :=
  Matrix.of (fun j k => (R.N X j k : ℤ))

lemma leftMulMatrixR_eq_map_leftMulMatrixZ (X : ι) :
    R.leftMulMatrixR X = (R.leftMulMatrixZ X).map (algebraMap ℤ ℝ) := by
  ext j k
  simp [leftMulMatrixR, leftMulMatrixZ, Matrix.map_apply, Matrix.of_apply]

theorem sum_N_pos (X j : ι) : 0 < ∑ k : ι, R.N X j k := by
  have h := R.assoc X j (R.star j) X
  have h1 : R.N j (R.star j) R.unit = 1 := by rw [R.duality]; simp
  have h2 : R.N X R.unit X = 1 := by rw [R.mul_unit]; simp
  have h3 : 1 ≤ ∑ m : ι, R.N X j m * R.N m (R.star j) X := by
    calc 1 = R.N j (R.star j) R.unit * R.N X R.unit X := by rw [h1, h2]
      _ ≤ ∑ m, R.N j (R.star j) m * R.N X m X := Finset.single_le_sum
            (f := fun m => R.N j (R.star j) m * R.N X m X)
            (fun m _ => Nat.zero_le _) (Finset.mem_univ _)
      _ = ∑ m, R.N X j m * R.N m (R.star j) X := h.symm
  obtain ⟨m, hm⟩ : ∃ m, 0 < R.N X j m := by
    by_contra h_all; push Not at h_all
    have hz : ∀ m, R.N X j m = 0 := fun m => Nat.le_zero.mp (h_all m)
    have : ∑ m : ι, R.N X j m * R.N m (R.star j) X = 0 :=
      Finset.sum_eq_zero (fun m _ => by simp [hz m])
    omega
  exact lt_of_lt_of_le hm (Finset.single_le_sum (f := fun k => R.N X j k)
    (fun k _ => Nat.zero_le _) (Finset.mem_univ _))

theorem sum_N_pos' (j k : ι) : 0 < ∑ i : ι, R.N j i k := by
  simp_rw [R.N_star_transpose j _ k]; exact R.sum_N_pos (R.star j) k

theorem left_transitive (X Z : ι) : ∃ Y : ι, 0 < R.N X Y Z := by
  have h := R.sum_N_pos' X Z
  by_contra h_all; push Not at h_all
  have hz : ∀ i, R.N X i Z = 0 := fun i => Nat.le_zero.mp (h_all i)
  have : ∑ i : ι, R.N X i Z = 0 := Finset.sum_eq_zero (fun i _ => hz i)
  omega

theorem right_transitive (X Z : ι) : ∃ Y : ι, 0 < R.N Y X Z := by

  have hassoc := R.assoc Z (R.star X) X Z

  have h1 : R.N (R.star X) X R.unit = 1 := by
    rw [R.duality]; simp [R.star_star]
  have h2 : R.N Z R.unit Z = 1 := by
    rw [R.mul_unit]; simp
  have h3 : 1 ≤ ∑ m : ι, R.N (R.star X) X m * R.N Z m Z := by
    calc 1 = R.N (R.star X) X R.unit * R.N Z R.unit Z := by rw [h1, h2]
      _ ≤ ∑ m, R.N (R.star X) X m * R.N Z m Z := Finset.single_le_sum
            (f := fun m => R.N (R.star X) X m * R.N Z m Z)
            (fun m _ => Nat.zero_le _) (Finset.mem_univ _)

  have h4 : 1 ≤ ∑ m : ι, R.N Z (R.star X) m * R.N m X Z := by linarith [hassoc]

  obtain ⟨m, hm⟩ : ∃ m, 0 < R.N m X Z := by
    by_contra h_all; push Not at h_all
    have hz : ∀ m, R.N m X Z = 0 := fun m => Nat.le_zero.mp (h_all m)
    have : ∑ m : ι, R.N Z (R.star X) m * R.N m X Z = 0 :=
      Finset.sum_eq_zero (fun m _ => by simp [hz m])
    omega
  exact ⟨m, hm⟩

theorem isTransitive : R.IsTransitive :=
  ⟨R.left_transitive, R.right_transitive⟩

theorem perron_frobenius_fusion_ring [Nonempty ι] [HasPerronFrobeniusProperty ι] :
    ∃ (d : ι → ℝ),
      d R.unit = 1 ∧
      (∀ i, d i > 0) ∧
      (∀ i j, d i * d j = ∑ k : ι, (R.N i j k : ℝ) * d k) := by

  have hMR_pos : ∀ j k, (0 : ℝ) < R.rightMulMatrix j k := by
    intro j k; simp only [rightMulMatrix, Matrix.of_apply]; exact_mod_cast R.sum_N_pos' j k

  let pf := perron_frobenius_pos_matrix R.rightMulMatrix hMR_pos
  let v := pf.evec
  have hv_pos : ∀ i, (0 : ℝ) < v i := pf.evec_pos
  have hv_unit_pos : (0 : ℝ) < v R.unit := hv_pos R.unit
  have hv_unit_ne : (v R.unit : ℝ) ≠ 0 := ne_of_gt hv_unit_pos

  have h_comm : ∀ X, R.leftMulMatrixR X * R.rightMulMatrix =
      R.rightMulMatrix * R.leftMulMatrixR X := by
    intro X; ext j l
    simp only [Matrix.mul_apply, leftMulMatrixR, rightMulMatrix, Matrix.of_apply]
    have h_nat : ∀ X' j' l' : ι,
        ∑ k : ι, R.N X' j' k * (∑ i : ι, R.N k i l') =
        ∑ k : ι, (∑ i : ι, R.N j' i k) * R.N X' k l' := by
      intro X' j' l'
      conv_lhs => arg 2; ext k; rw [Finset.mul_sum]
      conv_rhs => arg 2; ext k; rw [Finset.sum_mul]
      rw [Finset.sum_comm]; conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun a _ => R.assoc X' j' a l')
    exact_mod_cast h_nat X j l

  have h_NX_eigvec : ∀ X,
      R.rightMulMatrix.mulVec ((R.leftMulMatrixR X).mulVec v) =
      pf.ev • ((R.leftMulMatrixR X).mulVec v) := by
    intro X
    rw [Matrix.mulVec_mulVec, ← h_comm X, ← Matrix.mulVec_mulVec,
        pf.is_eigenvec, Matrix.mulVec_smul]
  have h_NX_pos : ∀ X j, 0 < ((R.leftMulMatrixR X).mulVec v) j := by
    intro X j
    simp only [leftMulMatrixR, Matrix.mulVec, dotProduct, Matrix.of_apply]
    obtain ⟨m, hm⟩ : ∃ m, 0 < R.N X j m := by
      have := R.sum_N_pos X j
      by_contra h_all; push Not at h_all
      have hz : ∀ m, R.N X j m = 0 := fun m => Nat.le_zero.mp (h_all m)
      have : ∑ m : ι, R.N X j m = 0 := Finset.sum_eq_zero (fun m _ => hz m)
      omega
    exact lt_of_lt_of_le
      (mul_pos (show (0:ℝ) < (R.N X j m : ℝ) from by exact_mod_cast hm) (hv_pos m))
      (Finset.single_le_sum (f := fun k => (R.N X j k : ℝ) * v k)
        (fun k _ => mul_nonneg (Nat.cast_nonneg _) (le_of_lt (hv_pos k)))
        (Finset.mem_univ _))

  have h_prop : ∀ X, ∃ c : ℝ, ∀ i, ((R.leftMulMatrixR X).mulVec v) i = c * v i :=
    fun X => pf.unique pf.ev _ (h_NX_pos X) (h_NX_eigvec X)

  refine ⟨fun X => v X / v R.unit, div_self hv_unit_ne,
    fun i => div_pos (hv_pos i) hv_unit_pos, ?_⟩

  intro X Y
  obtain ⟨cX, hcX⟩ := h_prop X

  have h_unit : (R.leftMulMatrixR X).mulVec v R.unit = v X := by
    simp only [leftMulMatrixR, Matrix.mulVec, dotProduct, Matrix.of_apply]
    simp_rw [R.mul_unit]; simp

  have h_cX : cX = v X / v R.unit := by
    have h := hcX R.unit; rw [h_unit] at h
    field_simp at h ⊢; linarith

  have h_key : ∑ k : ι, (R.N X Y k : ℝ) * v k = v X / v R.unit * v Y := by
    have h := hcX Y
    simp only [leftMulMatrixR, Matrix.mulVec, dotProduct, Matrix.of_apply] at h
    rw [h_cX] at h; exact h


  show v X / v R.unit * (v Y / v R.unit) = ∑ k : ι, (R.N X Y k : ℝ) * (v k / v R.unit)
  simp_rw [mul_div_assoc']
  rw [← Finset.sum_div, h_key]

theorem d_star_of_d_mul [Nonempty ι]
    (d : ι → ℝ) (d_pos : ∀ i, d i > 0)
    (d_mul : ∀ i j, d i * d j = ∑ k : ι, (R.N i j k : ℝ) * d k)
    (i : ι) : d (R.star i) = d i := by

  have S_pos : (0 : ℝ) < ∑ j : ι, d j ^ 2 := Finset.sum_pos
    (fun j _ => sq_pos_of_pos (d_pos j)) Finset.univ_nonempty

  have key_i : d i * (∑ j : ι, d j ^ 2) =
      ∑ j : ι, ∑ k : ι, (R.N i j k : ℝ) * d j * d k := by
    conv_lhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    calc d i * (d j ^ 2)
        = (d i * d j) * d j := by ring
      _ = (∑ k, (R.N i j k : ℝ) * d k) * d j := by rw [d_mul i j]
      _ = ∑ k, (R.N i j k : ℝ) * d j * d k := by
          rw [Finset.sum_mul]; congr 1; ext k; ring

  have key_si : d (R.star i) * (∑ j : ι, d j ^ 2) =
      ∑ j : ι, ∑ k : ι, (R.N (R.star i) j k : ℝ) * d j * d k := by
    conv_lhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    calc d (R.star i) * (d j ^ 2)
        = (d (R.star i) * d j) * d j := by ring
      _ = (∑ k, (R.N (R.star i) j k : ℝ) * d k) * d j := by rw [d_mul (R.star i) j]
      _ = ∑ k, (R.N (R.star i) j k : ℝ) * d j * d k := by
          rw [Finset.sum_mul]; congr 1; ext k; ring

  have hN : ∀ j k, (R.N (R.star i) j k : ℝ) = (R.N i k j : ℝ) := by
    intro j k
    have := R.N_star_transpose (R.star i) j k
    rw [R.star_star] at this
    exact congrArg Nat.cast this

  have swap : ∑ j : ι, ∑ k : ι, (R.N (R.star i) j k : ℝ) * d j * d k =
              ∑ j : ι, ∑ k : ι, (R.N i j k : ℝ) * d j * d k := by
    conv_lhs => arg 2; ext j; arg 2; ext k; rw [hN j k]

    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro j _
    ring

  exact (mul_right_cancel₀ (ne_of_gt S_pos) (by rw [key_i, key_si, swap])).symm

theorem exists_FPdimData [Nonempty ι] [HasPerronFrobeniusProperty ι] : Nonempty R.FPdimData := by
  obtain ⟨d, hunit, hpos, hmul⟩ := perron_frobenius_fusion_ring R
  exact ⟨{
    d := d
    d_unit := hunit
    d_pos := hpos
    d_mul := hmul
  }⟩

variable {R}

namespace FPdimData

variable (fpd : R.FPdimData)

theorem d_star [Nonempty ι] (i : ι) : fpd.d (R.star i) = fpd.d i :=
  d_star_of_d_mul R fpd.d fpd.d_pos fpd.d_mul i

noncomputable def FPdim : ι → ℝ := fpd.d

theorem d_ge_one (i : ι) : fpd.d i ≥ 1 := by
  haveI : Nonempty ι := ⟨i⟩
  have hdi_pos := fpd.d_pos i

  have hmul := fpd.d_mul i (R.star i)

  rw [fpd.d_star] at hmul

  have hdual : R.N i (R.star i) R.unit = 1 := by
    rw [R.duality]; simp

  have hterm : (R.N i (R.star i) R.unit : ℝ) * fpd.d R.unit = 1 := by
    rw [hdual, fpd.d_unit]; simp

  set f := fun k => (R.N i (R.star i) k : ℝ) * fpd.d k
  have hle : f R.unit ≤ ∑ k : ι, f k :=
    Finset.single_le_sum
      (fun k _ => mul_nonneg (Nat.cast_nonneg _) (le_of_lt (fpd.d_pos k)))
      (Finset.mem_univ _)

  have hsq : fpd.d i * fpd.d i ≥ 1 := by rw [hmul]; linarith

  nlinarith [sq_nonneg (fpd.d i - 1)]

noncomputable def catDim : ℝ :=
  ∑ i : ι, fpd.d i ^ 2

theorem catDim_pos [Nonempty ι] : fpd.catDim > 0 := by
  unfold catDim
  apply Finset.sum_pos
  · intro i _; exact sq_pos_of_pos (fpd.d_pos i)
  · exact Finset.univ_nonempty

theorem catDim_ge_card : fpd.catDim ≥ (Fintype.card ι : ℝ) := by
  unfold catDim
  have hcard : (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  linarith [Finset.sum_le_sum (fun (i : ι) (_hi : i ∈ Finset.univ) =>
    show (1 : ℝ) ≤ fpd.d i ^ 2 from by
      nlinarith [fpd.d_ge_one i, sq_nonneg (fpd.d i - 1)])]

theorem fpDim_unique_character [Nonempty ι]
    [HasPerronFrobeniusProperty ι]
    (χ : ι → ℝ) (hχ_unit : χ R.unit = 1) (hχ_pos : ∀ i, χ i > 0)
    (hχ_mul : ∀ i j, χ i * χ j = ∑ k : ι, (R.N i j k : ℝ) * χ k) :
    ∀ i, χ i = fpd.d i := by


  have hMR_pos : ∀ j k, (0 : ℝ) < R.rightMulMatrix j k := by
    intro j k; simp only [rightMulMatrix, Matrix.of_apply]; exact_mod_cast R.sum_N_pos' j k

  have hd_eig : R.rightMulMatrix.mulVec fpd.d = (∑ i : ι, fpd.d i) • fpd.d := by
    ext j; simp only [Matrix.mulVec, dotProduct, rightMulMatrix, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul]
    calc ∑ k, (∑ i, (R.N j i k : ℝ)) * fpd.d k
        = ∑ k, ∑ i, (R.N j i k : ℝ) * fpd.d k := by
          congr 1; ext k; rw [Finset.sum_mul]
      _ = ∑ i, ∑ k, (R.N j i k : ℝ) * fpd.d k := Finset.sum_comm
      _ = ∑ i, fpd.d j * fpd.d i := by
          congr 1; ext i; rw [← fpd.d_mul j i]
      _ = fpd.d j * ∑ i, fpd.d i := by rw [← Finset.mul_sum]
      _ = (∑ i, fpd.d i) * fpd.d j := by ring

  have hχ_eig : R.rightMulMatrix.mulVec χ = (∑ i : ι, χ i) • χ := by
    ext j; simp only [Matrix.mulVec, dotProduct, rightMulMatrix, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul]
    calc ∑ k, (∑ i, (R.N j i k : ℝ)) * χ k
        = ∑ k, ∑ i, (R.N j i k : ℝ) * χ k := by
          congr 1; ext k; rw [Finset.sum_mul]
      _ = ∑ i, ∑ k, (R.N j i k : ℝ) * χ k := Finset.sum_comm
      _ = ∑ i, χ j * χ i := by
          congr 1; ext i; rw [← hχ_mul j i]
      _ = χ j * ∑ i, χ i := by rw [← Finset.mul_sum]
      _ = (∑ i, χ i) * χ j := by ring

  obtain ⟨c, hc⟩ := HasPerronFrobeniusProperty.pfUnique R.rightMulMatrix hMR_pos
    (∑ i, fpd.d i) (∑ i, χ i) fpd.d χ fpd.d_pos hd_eig hχ_pos hχ_eig

  have hc_unit := hc R.unit
  rw [hχ_unit, fpd.d_unit, mul_one] at hc_unit
  intro i; rw [hc i, ← hc_unit, one_mul]

theorem d_is_eigenvalue_of_mulMatrix (i : ι) :
    (R.leftMulMatrixR i).mulVec fpd.d = fpd.d i • fpd.d := by
  ext j
  simp only [leftMulMatrixR, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [← fpd.d_mul i j]

theorem d_right_mul (j Y : ι) :
    ∑ k, (R.N j Y k : ℝ) * fpd.d k = fpd.d j * fpd.d Y :=
  (fpd.d_mul j Y).symm

theorem d_unique_positive_eigenvector [Nonempty ι] [HasPerronFrobeniusProperty ι]
    (w : ι → ℝ) (hw_pos : ∀ i, 0 < w i) (r : ℝ)
    (hw_eig : R.rightMulMatrix.mulVec w = r • w) :
    ∃ c : ℝ, ∀ i, w i = c * fpd.d i := by
  have hMR_pos : ∀ j k, (0 : ℝ) < R.rightMulMatrix j k := by
    intro j k; simp only [rightMulMatrix, Matrix.of_apply]; exact_mod_cast R.sum_N_pos' j k
  have hd_eig : R.rightMulMatrix.mulVec fpd.d = (∑ i : ι, fpd.d i) • fpd.d := by
    ext j; simp only [Matrix.mulVec, dotProduct, rightMulMatrix, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul]
    calc ∑ k, (∑ i, (R.N j i k : ℝ)) * fpd.d k
        = ∑ k, ∑ i, (R.N j i k : ℝ) * fpd.d k := by
          congr 1; ext k; rw [Finset.sum_mul]
      _ = ∑ i, ∑ k, (R.N j i k : ℝ) * fpd.d k := Finset.sum_comm
      _ = ∑ i, fpd.d j * fpd.d i := by
          congr 1; ext i; rw [← fpd.d_mul j i]
      _ = fpd.d j * ∑ i, fpd.d i := by rw [← Finset.mul_sum]
      _ = (∑ i, fpd.d i) * fpd.d j := by ring
  exact HasPerronFrobeniusProperty.pfUnique R.rightMulMatrix hMR_pos
    (∑ i, fpd.d i) r fpd.d w fpd.d_pos hd_eig hw_pos hw_eig

theorem d_dominates_eigenvalues [Nonempty ι] (i : ι) (μ : ℂ)
    (hμ : IsComplexEigenvalue (R.leftMulMatrixR i) μ) :
    ‖μ‖ ≤ fpd.d i := by
  have hM : ∀ j k, 0 ≤ (R.leftMulMatrixR i) j k := by
    intro j k; simp only [leftMulMatrixR, Matrix.of_apply]; exact Nat.cast_nonneg _
  exact perron_frobenius_spectral_dominance _ hM _ _ fpd.d_pos
    (fpd.d_is_eigenvalue_of_mulMatrix i) μ hμ

theorem d_eq_one_invertible (i : ι) (hi : fpd.d i = 1) :
    ∀ k, k ≠ R.unit → R.N i (R.star i) k = 0 := by
  haveI : Nonempty ι := ⟨i⟩

  have hmul := fpd.d_mul i (R.star i)
  rw [hi, fpd.d_star, hi, one_mul] at hmul

  have hdual : R.N i (R.star i) R.unit = 1 := by rw [R.duality]; simp
  have hterm : (R.N i (R.star i) R.unit : ℝ) * fpd.d R.unit = 1 := by
    rw [hdual, fpd.d_unit]; simp

  have h_nonneg : ∀ k, 0 ≤ (R.N i (R.star i) k : ℝ) * fpd.d k :=
    fun k => mul_nonneg (Nat.cast_nonneg _) (le_of_lt (fpd.d_pos k))

  have hle : (R.N i (R.star i) R.unit : ℝ) * fpd.d R.unit ≤
      ∑ k : ι, (R.N i (R.star i) k : ℝ) * fpd.d k :=
    Finset.single_le_sum (fun k _ => h_nonneg k) (Finset.mem_univ _)

  intro k hk

  have h_zero : (R.N i (R.star i) k : ℝ) * fpd.d k = 0 := by

    have herase : ∑ m ∈ Finset.univ.erase R.unit,
        (R.N i (R.star i) m : ℝ) * fpd.d m = ∑ m : ι, (R.N i (R.star i) m : ℝ) * fpd.d m -
        (R.N i (R.star i) R.unit : ℝ) * fpd.d R.unit :=
      Finset.sum_erase_eq_sub (Finset.mem_univ _)

    have herase_zero : ∑ m ∈ Finset.univ.erase R.unit,
        (R.N i (R.star i) m : ℝ) * fpd.d m = 0 := by linarith

    have hk_mem : k ∈ Finset.univ.erase R.unit :=
      Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩

    have hle_k := Finset.single_le_sum (fun m _ => h_nonneg m) hk_mem
    linarith [h_nonneg k]

  cases mul_eq_zero.mp h_zero with
  | inl h => exact_mod_cast h
  | inr h => exact absurd h (ne_of_gt (fpd.d_pos k))

theorem d_eq_one_of_invertible (i : ι)
    (h_inv : ∀ k, k ≠ R.unit → R.N i (R.star i) k = 0) :
    fpd.d i = 1 := by
  haveI : Nonempty ι := ⟨i⟩
  have hmul := fpd.d_mul i (R.star i)
  rw [fpd.d_star] at hmul

  have hsum : ∑ k : ι, (R.N i (R.star i) k : ℝ) * fpd.d k =
      (R.N i (R.star i) R.unit : ℝ) * fpd.d R.unit := by
    apply Finset.sum_eq_single
    · intro k _ hk; rw [h_inv k hk]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [R.duality, if_pos rfl, fpd.d_unit] at hsum; simp at hsum

  rw [hsum] at hmul

  have hdi_pos := fpd.d_pos i
  nlinarith [sq_nonneg (fpd.d i - 1)]

theorem corollary_1_45_9 (i : ι) :
    fpd.d i = 1 ↔ (∀ k, k ≠ R.unit → R.N i (R.star i) k = 0) :=
  ⟨fpd.d_eq_one_invertible i, fpd.d_eq_one_of_invertible i⟩

theorem proposition_1_45_5_part1 :
    fpd.d R.unit = 1 ∧
    (∀ i j, fpd.d i * fpd.d j = ∑ k : ι, (R.N i j k : ℝ) * fpd.d k) :=
  ⟨fpd.d_unit, fpd.d_mul⟩

theorem proposition_1_45_5_part2 [Nonempty ι] [HasPerronFrobeniusProperty ι] :

    (∀ X, (R.leftMulMatrixR X).mulVec fpd.d = fpd.d X • fpd.d) ∧

    (∀ i, fpd.d i > 0) ∧

    (fpd.catDim > 0) ∧

    (∀ j Y, ∑ k, (R.N j Y k : ℝ) * fpd.d k = fpd.d j * fpd.d Y) ∧

    (∀ (w : ι → ℝ) (r : ℝ), (∀ i, 0 < w i) →
      R.rightMulMatrix.mulVec w = r • w →
      ∃ c : ℝ, ∀ i, w i = c * fpd.d i) :=
  ⟨fpd.d_is_eigenvalue_of_mulMatrix, fpd.d_pos, fpd.catDim_pos,
   fpd.d_right_mul,
   fun w r hw_pos hw_eig => fpd.d_unique_positive_eigenvector w hw_pos r hw_eig⟩

theorem proposition_1_45_5_part3 [Nonempty ι]
    [HasPerronFrobeniusProperty ι]
    (χ : ι → ℝ) (hχ_unit : χ R.unit = 1) (hχ_nonneg : ∀ i, 0 ≤ χ i)
    (hχ_mul : ∀ i j, χ i * χ j = ∑ k : ι, (R.N i j k : ℝ) * χ k) :
    ∀ i, χ i = fpd.d i := by


  have hχ_pos : ∀ i, χ i > 0 := by
    intro k
    have hprod : χ k * χ (R.star k) ≥ 1 := by
      have hmul := hχ_mul k (R.star k)
      rw [hmul]
      have hdual : R.N k (R.star k) R.unit = 1 := by
        rw [R.duality]; simp
      calc ∑ m : ι, (R.N k (R.star k) m : ℝ) * χ m
          ≥ (R.N k (R.star k) R.unit : ℝ) * χ R.unit :=
          Finset.single_le_sum (f := fun m => (R.N k (R.star k) m : ℝ) * χ m)
            (fun m _ => mul_nonneg (Nat.cast_nonneg _) (hχ_nonneg m)) (Finset.mem_univ R.unit)
        _ = 1 := by simp [hdual, hχ_unit]
    nlinarith [hχ_nonneg k, hχ_nonneg (R.star k)]
  exact fpd.fpDim_unique_character χ hχ_unit hχ_pos hχ_mul

theorem proposition_1_45_5_part4 (i : ι) :
    (R.leftMulMatrixR i).mulVec fpd.d = fpd.d i • fpd.d :=
  fpd.d_is_eigenvalue_of_mulMatrix i

theorem proposition_1_45_5 :
    (fpd.d R.unit = 1 ∧
     (∀ i j, fpd.d i * fpd.d j = ∑ k : ι, (R.N i j k : ℝ) * fpd.d k)) ∧
    (∀ X, (R.leftMulMatrixR X).mulVec fpd.d = fpd.d X • fpd.d) ∧
    (∀ i, fpd.d i > 0) :=
  ⟨⟨fpd.d_unit, fpd.d_mul⟩, fpd.d_is_eigenvalue_of_mulMatrix, fpd.d_pos⟩

theorem fpdim_antiAut_invariant (ψ : ι → ι) (hψ : R.IsAntiAutomorphism ψ)
    (i : ι) : fpd.d (ψ i) = fpd.d i := by
  haveI : Nonempty ι := ⟨i⟩

  have S_pos : (0 : ℝ) < ∑ j : ι, fpd.d j ^ 2 := Finset.sum_pos
    (fun j _ => sq_pos_of_pos (fpd.d_pos j)) Finset.univ_nonempty

  have key_i : fpd.d i * (∑ j : ι, fpd.d j ^ 2) =
      ∑ j : ι, ∑ k : ι, (R.N i j k : ℝ) * fpd.d j * fpd.d k := by
    conv_lhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    calc fpd.d i * (fpd.d j ^ 2)
        = (fpd.d i * fpd.d j) * fpd.d j := by ring
      _ = (∑ k, (R.N i j k : ℝ) * fpd.d k) * fpd.d j := by rw [fpd.d_mul i j]
      _ = ∑ k, (R.N i j k : ℝ) * fpd.d j * fpd.d k := by
          rw [Finset.sum_mul]; congr 1; ext k; ring

  have key_psi : fpd.d (ψ i) * (∑ j : ι, fpd.d j ^ 2) =
      ∑ j : ι, ∑ k : ι, (R.N (ψ i) j k : ℝ) * fpd.d j * fpd.d k := by
    conv_lhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    calc fpd.d (ψ i) * (fpd.d j ^ 2)
        = (fpd.d (ψ i) * fpd.d j) * fpd.d j := by ring
      _ = (∑ k, (R.N (ψ i) j k : ℝ) * fpd.d k) * fpd.d j := by rw [fpd.d_mul (ψ i) j]
      _ = ∑ k, (R.N (ψ i) j k : ℝ) * fpd.d j * fpd.d k := by
          rw [Finset.sum_mul]; congr 1; ext k; ring

  have hN : ∀ j k, (R.N (ψ i) j k : ℝ) = (R.N i k j : ℝ) := by
    intro j k
    exact congrArg Nat.cast (hψ.2 i j k)

  have swap : ∑ j : ι, ∑ k : ι, (R.N (ψ i) j k : ℝ) * fpd.d j * fpd.d k =
              ∑ j : ι, ∑ k : ι, (R.N i j k : ℝ) * fpd.d j * fpd.d k := by
    conv_lhs => arg 2; ext j; arg 2; ext k; rw [hN j k]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro j _
    ring

  exact (mul_right_cancel₀ (ne_of_gt S_pos) (by rw [key_i, key_psi, swap])).symm

theorem isIntegral_d (i : ι) : IsIntegral ℤ (fpd.d i) := by
  haveI : Nonempty ι := ⟨R.unit⟩
  set M := R.leftMulMatrixR i
  set MZ := R.leftMulMatrixZ i
  have hmap : M = MZ.map (algebraMap ℤ ℝ) := R.leftMulMatrixR_eq_map_leftMulMatrixZ i
  have hv := fpd.d_is_eigenvalue_of_mulMatrix i
  have hne : fpd.d ≠ 0 := by
    intro h
    have := fpd.d_pos (Classical.arbitrary ι)
    rw [congr_fun h] at this
    exact lt_irrefl 0 this

  have hker : (Matrix.scalar ι (fpd.d i) - M).mulVec fpd.d = 0 := by
    rw [Matrix.sub_mulVec, hv]
    simp only [Matrix.scalar_apply]
    simp

  have hdet : (Matrix.scalar ι (fpd.d i) - M).det = 0 := by
    by_contra hdet
    have hunit_det : IsUnit (Matrix.scalar ι (fpd.d i) - M).det := IsUnit.mk0 _ hdet
    have hunit : IsUnit (Matrix.scalar ι (fpd.d i) - M) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr hunit_det
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
    exact hne (hinj (hker.trans (map_zero (Matrix.scalar ι (fpd.d i) - M).mulVecLin).symm))

  have heval : Polynomial.eval (fpd.d i) M.charpoly = 0 := by
    rwa [Matrix.eval_charpoly]

  have hcharpoly : M.charpoly = MZ.charpoly.map (algebraMap ℤ ℝ) := by
    rw [hmap, Matrix.charpoly_map]

  have heval2 : Polynomial.eval₂ (algebraMap ℤ ℝ) (fpd.d i) MZ.charpoly = 0 := by
    rw [← Polynomial.eval_map, ← hcharpoly]
    exact heval
  exact ⟨MZ.charpoly, Matrix.charpoly_monic MZ, heval2⟩

theorem isIntegral_d_sq (i : ι) : IsIntegral ℤ (fpd.d i ^ 2) :=
  (fpd.isIntegral_d i).pow 2

theorem isIntegral_catDim : IsIntegral ℤ fpd.catDim := by
  apply IsIntegral.sum
  intro i _
  exact fpd.isIntegral_d_sq i

theorem proposition_1_45_4 [Nonempty ι] (i : ι) :
    IsIntegral ℤ (fpd.d i) ∧
    (∀ μ : ℂ, IsComplexEigenvalue (R.leftMulMatrixR i) μ → ‖μ‖ ≤ fpd.d i) ∧
    fpd.d i ≥ 1 :=
  ⟨fpd.isIntegral_d i, fpd.d_dominates_eigenvalues i, fpd.d_ge_one i⟩

end FPdimData

end FPdim

end FusionRing

section Kronecker

open Real FusionRing
open scoped Matrix

theorem kronecker_theorem (q : ℂ) (hq_int : IsIntegral ℤ q)
    (hq_norm : ‖q‖ = 1)
    (hq_conj : ∀ β : ℂ, Polynomial.aeval β (minpoly ℤ q) = 0 → ‖β‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ q ^ n = 1 := by
  open Polynomial IntermediateField in
  have hq_intQ : IsIntegral ℚ q := hq_int.tower_top
  let K := ℚ⟮q⟯
  have : NumberField K := {
    to_charZero := ℚ⟮q⟯.charZero
    to_finiteDimensional := adjoin.finiteDimensional hq_intQ }
  let y : K := ⟨q, mem_adjoin_simple_self ℚ q⟩
  suffices ∃ (n : ℕ) (_ : 0 < n), y ^ n = 1 by
    obtain ⟨n, hn₀, hn₁⟩ := this
    exact ⟨n, hn₀, congrArg (algebraMap K ℂ) hn₁⟩
  refine NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ ?hxi ?hx
  · exact coe_isIntegral_iff.mp hq_int
  · intro φ

    have h_root_y : aeval (φ y) (minpoly ℚ y) = 0 := by
      have := aeval_algHom_apply φ.toRatAlgHom y (minpoly ℚ y)
      simp [minpoly.aeval] at this; exact this

    have h_minpoly_Z_Q : minpoly ℚ q = (minpoly ℤ q).map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hq_int

    have h_minpoly_eq : minpoly ℚ q = minpoly ℚ y := by
      rw [show q = (algebraMap K ℂ) y from rfl]
      exact minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ K ℂ)
        (algebraMap K ℂ).injective y

    have h_root_mapped : aeval (φ y) ((minpoly ℤ q).map (algebraMap ℤ ℚ)) = 0 := by
      rw [← h_minpoly_Z_Q, h_minpoly_eq]; exact h_root_y

    have h_root_Z : aeval (φ y) (minpoly ℤ q) = 0 := by
      rwa [aeval_map_algebraMap] at h_root_mapped
    exact hq_conj (φ y) h_root_Z

lemma norm_eq_one_of_quadratic_bounded (β : ℂ) (μ : ℝ) (hμ : |μ| < 2)
    (hpoly : β ^ 2 - (↑μ : ℂ) * β + 1 = 0) : ‖β‖ = 1 := by
  have hre_eq : (β ^ 2).re = β.re ^ 2 - β.im ^ 2 := by
    simp [sq, Complex.mul_re]
  have him_eq : (β ^ 2).im = 2 * β.re * β.im := by
    simp [sq, Complex.mul_im]; ring
  have hre : β.re ^ 2 - β.im ^ 2 - μ * β.re + 1 = 0 := by
    have h := congr_arg Complex.re hpoly
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.zero_re] at h
    nlinarith [hre_eq]
  have him : 2 * β.re * β.im - μ * β.im = 0 := by
    have h := congr_arg Complex.im hpoly
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_im, Complex.zero_im] at h
    nlinarith [him_eq]
  have him_factor : β.im * (2 * β.re - μ) = 0 := by linarith
  rcases mul_eq_zero.mp him_factor with him_zero | hre_eq_half
  · exfalso
    have hreal : β.re ^ 2 - μ * β.re + 1 = 0 := by nlinarith
    have hdisc : μ ^ 2 - 4 < 0 := by nlinarith [abs_lt.mp hμ]
    nlinarith [sq_nonneg (β.re - μ / 2)]
  · have hre_val : β.re = μ / 2 := by linarith
    have him_sq : β.im ^ 2 = β.re ^ 2 - μ * β.re + 1 := by linarith
    have hns : Complex.normSq β = 1 := by
      simp only [Complex.normSq_apply]; rw [hre_val]; nlinarith
    show Real.sqrt (Complex.normSq β) = 1
    rw [hns, Real.sqrt_one]






lemma cos_two_pi_mul_div_le (m k : ℕ) (hm : 2 ≤ m) (hk1 : 1 ≤ k) (hk_lt : k < m) :
    cos (2 * π * ↑k / ↑m) ≤ cos (2 * π / ↑m) := by
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (by omega)
  have hm_ne : (↑m : ℝ) ≠ 0 := ne_of_gt hm_pos
  by_cases h : 2 * k ≤ m
  · apply cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · rw [div_le_iff₀ hm_pos]
      nlinarith [pi_pos, (show (2 * (↑k : ℝ)) ≤ ↑m from by exact_mod_cast h)]
    · apply div_le_div_of_nonneg_right _ hm_pos.le
      nlinarith [(show (1 : ℝ) ≤ ↑k from by exact_mod_cast hk1), pi_pos]
  · push Not at h
    have hmk : k ≤ m := le_of_lt hk_lt
    have h2mk : 2 * (m - k) ≤ m := by omega
    have h_eq : cos (2 * π * ↑k / ↑m) = cos (2 * π * ↑(m - k) / ↑m) := by
      rw [Nat.cast_sub hmk]; simp only [mul_sub, sub_div]
      rw [show 2 * π * ↑m / ↑m = 2 * π from by field_simp, cos_two_pi_sub]
    rw [h_eq]
    apply cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · rw [div_le_iff₀ hm_pos]
      nlinarith [pi_pos, (show (2 * (↑(m - k) : ℝ)) ≤ ↑m from by exact_mod_cast h2mk)]
    · apply div_le_div_of_nonneg_right _ hm_pos.le
      nlinarith [(show (1 : ℝ) ≤ ↑(m - k) from by exact_mod_cast (show 1 ≤ m - k by omega)),
                 pi_pos]


lemma cos_two_pi_p_div_odd (p : ℕ) :
    cos (2 * π * ↑p / (2 * ↑p + 1)) = -cos (π / (2 * ↑p + 1)) := by
  have h : 2 * π * ↑p / (2 * ↑p + 1) = π - π / (2 * ↑p + 1) := by
    have h2p1 : (2 * ↑p + 1 : ℝ) ≠ 0 := by positivity
    field_simp; ring
  rw [h, cos_pi_sub]

lemma cos_pi_div_2p1_pos (p : ℕ) (hp : 1 ≤ p) :
    0 < cos (π / (2 * ↑p + 1)) := by
  apply cos_pos_of_mem_Ioo
  have h2p1_pos : (0:ℝ) < 2 * ↑p + 1 := by positivity
  have hp_cast : (1:ℝ) ≤ (↑p : ℝ) := Nat.one_le_cast.mpr hp
  have hpi_div_pos : 0 < π / (2 * ↑p + 1) := div_pos pi_pos h2p1_pos
  refine ⟨by linarith [neg_lt_zero.mpr (div_pos pi_pos two_pos)], ?_⟩
  rw [div_lt_div_iff₀ h2p1_pos two_pos]
  nlinarith [pi_pos]

lemma cos_pi_div_odd_lt (p : ℕ) (hp : 1 ≤ p) :
    cos (2 * π / (2 * ↑p + 1)) < cos (π / (2 * ↑p + 1)) := by
  have h2p1_pos : (0:ℝ) < 2 * ↑p + 1 := by positivity
  have hp_cast : (1:ℝ) ≤ (↑p : ℝ) := Nat.one_le_cast.mpr hp
  apply cos_lt_cos_of_nonneg_of_le_pi
  · positivity
  · rw [div_le_iff₀ h2p1_pos]; nlinarith [pi_pos]
  · exact div_lt_div_of_pos_right (by linarith [pi_pos]) h2p1_pos

lemma coprime_p_two_p_succ (p : ℕ) : Nat.Coprime p (2 * p + 1) := by
  rw [Nat.Coprime, Nat.gcd_comm, show 2 * p + 1 = 1 + p + p from by ring]
  simp

lemma odd_m_violates_dominance (p : ℕ) (hp : 1 ≤ p) :
    2 * cos (2 * π / (2 * ↑p + 1)) <
    |2 * cos (2 * π * ↑p / (2 * ↑p + 1))| := by
  rw [cos_two_pi_p_div_odd]
  simp only [mul_neg, abs_neg]
  have hcp := cos_pi_div_2p1_pos p hp
  rw [abs_of_pos (by linarith : 0 < 2 * cos (π / (2 * ↑p + 1)))]
  linarith [cos_pi_div_odd_lt p hp]

lemma ev_nonneg_of_nonneg_matrix_pos_eigvec
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (B : Matrix ι ι ℕ) (ev : ℝ) (v : ι → ℝ)
    (hv_pos : ∀ i, 0 < v i)
    (hv_eig : (B.map (Nat.cast : ℕ → ℝ)).mulVec v = ev • v) :
    0 ≤ ev := by
  have hi := Classical.arbitrary ι
  have hvi : 0 < v hi := hv_pos hi
  have hmv : 0 ≤ (B.map (Nat.cast : ℕ → ℝ)).mulVec v hi := by
    simp only [Matrix.mulVec, Matrix.map_apply]
    apply Finset.sum_nonneg
    intro j _; exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (hv_pos j))
  have heq : (B.map (Nat.cast : ℕ → ℝ)).mulVec v hi = ev * v hi := by
    have := congr_fun hv_eig hi
    simp [Pi.smul_apply, smul_eq_mul] at this; exact this
  exact nonneg_of_mul_nonneg_left (heq ▸ hmv) hvi


end Kronecker

namespace PerronFrobeniusGeneral

open FusionRing

lemma sum_pos_mul_nonneg_eq_zero_imp {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (u : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hu : ∀ i, 0 ≤ u i)
    (hsum : ∑ i, a i * u i = 0) :
    ∀ i, u i = 0 := by
  intro i
  have h_nonneg : ∀ j, 0 ≤ a j * u j := fun j => mul_nonneg (le_of_lt (ha j)) (hu j)
  have h_le := Finset.single_le_sum (f := fun j => a j * u j)
    (fun j _ => h_nonneg j) (Finset.mem_univ i)
  have h_eq : a i * u i = 0 := le_antisymm (by linarith) (h_nonneg i)
  exact (mul_eq_zero.mp h_eq).resolve_left (ne_of_gt (ha i))

lemma mulVec_diff_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (r s : ℝ) (v w : ι → ℝ) (c : ℝ)
    (hev : M.mulVec v = r • v) (hew : M.mulVec w = s • w) (k : ι) :
    (∑ i, M k i * (w i - c * v i)) = s * w k - c * r * v k := by
  have h1 : ∑ i, M k i * w i = s * w k := by
    have := congr_fun hew k
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this; linarith
  have h2 : ∑ i, M k i * v i = r * v k := by
    have := congr_fun hev k
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this; linarith
  simp_rw [mul_sub]; rw [Finset.sum_sub_distrib]
  have h3 : ∑ x, M k x * (c * v x) = c * r * v k := by
    simp_rw [← mul_assoc, mul_comm (M k _) c, mul_assoc]; rw [← Finset.mul_sum, h2]
  linarith

theorem pfUnique_general {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j)
    (r₁ r₂ : ℝ) (v w : ι → ℝ)
    (hv : ∀ i, 0 < v i) (hev : M.mulVec v = r₁ • v)
    (hw : ∀ i, 0 < w i) (hew : M.mulVec w = r₂ • w) :
    ∃ c : ℝ, ∀ i, w i = c * v i := by

  obtain ⟨j, _, hj_min⟩ := Finset.exists_min_image Finset.univ (fun i => w i / v i)
    Finset.univ_nonempty
  set c := w j / v j
  have hc_pos : 0 < c := div_pos (hw j) (hv j)
  have hv_ne : ∀ i, v i ≠ 0 := fun i => ne_of_gt (hv i)
  have hw_ne : ∀ i, w i ≠ 0 := fun i => ne_of_gt (hw i)

  have hge : ∀ i, c * v i ≤ w i := by
    intro i
    have hi : c ≤ w i / v i := hj_min i (Finset.mem_univ i)
    rwa [le_div_iff₀ (hv i)] at hi
  have hu_nonneg : ∀ i, 0 ≤ w i - c * v i := fun i => by linarith [hge i]

  have hu_j : w j - c * v j = 0 := by
    show w j - w j / v j * v j = 0; rw [div_mul_cancel₀ (w j) (hv_ne j)]; ring
  have hw_j_eq : w j = c * v j := by linarith

  have hMu_j' : ∑ i, M j i * (w i - c * v i) = (r₂ - r₁) * c * v j := by
    rw [mulVec_diff_eq M r₁ r₂ v w c hev hew j, hw_j_eq]; ring
  have hMu_nonneg : 0 ≤ ∑ i, M j i * (w i - c * v i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (le_of_lt (hM j i)) (hu_nonneg i)
  have hr₂_ge : r₁ ≤ r₂ := by
    by_contra h; push Not at h
    have : (r₂ - r₁) * c * v j < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hc_pos) (hv j)
    linarith

  obtain ⟨k, _, hk_min⟩ := Finset.exists_min_image Finset.univ (fun i => v i / w i)
    Finset.univ_nonempty
  set d := v k / w k
  have hd_pos : 0 < d := div_pos (hv k) (hw k)
  have hge' : ∀ i, d * w i ≤ v i := by
    intro i
    have hi : d ≤ v i / w i := hk_min i (Finset.mem_univ i)
    rwa [le_div_iff₀ (hw i)] at hi
  have hu'_nonneg : ∀ i, 0 ≤ v i - d * w i := fun i => by linarith [hge' i]
  have hv_k_eq : v k = d * w k := by
    have : v k - d * w k = 0 := by
      show v k - v k / w k * w k = 0; rw [div_mul_cancel₀ (v k) (hw_ne k)]; ring
    linarith
  have hMu'_k' : ∑ i, M k i * (v i - d * w i) = (r₁ - r₂) * d * w k := by
    rw [mulVec_diff_eq M r₂ r₁ w v d hew hev k, hv_k_eq]; ring
  have hMu'_nonneg : 0 ≤ ∑ i, M k i * (v i - d * w i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (le_of_lt (hM k i)) (hu'_nonneg i)
  have hr₁_ge : r₂ ≤ r₁ := by
    by_contra h; push Not at h
    have : (r₁ - r₂) * d * w k < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hd_pos) (hw k)
    linarith

  have hr_eq : r₁ = r₂ := le_antisymm hr₂_ge hr₁_ge
  have hMu_zero : ∑ i, M j i * (w i - c * v i) = 0 := by rw [hMu_j']; simp [hr_eq]
  have hu_zero : ∀ i, w i - c * v i = 0 :=
    sum_pos_mul_nonneg_eq_zero_imp (M j ·) _ (hM j) hu_nonneg hMu_zero
  exact ⟨c, fun i => by linarith [hu_zero i]⟩

end PerronFrobeniusGeneral

namespace PerronFrobeniusFin1

open FusionRing

noncomputable instance : HasPerronFrobeniusProperty (Fin 1) where
  pfEigenvec := fun M hM => by
    refine ⟨M 0 0, fun _ => 1, hM 0 0, fun _ => one_pos, ?_⟩
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
    subst hi
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  pfUnique := fun M _ r₁ r₂ v w hv _ hw _ => by
    exact ⟨w 0 / v 0, fun i => by
      have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
      subst hi; rw [div_mul_cancel₀ _ (ne_of_gt (hv 0))]⟩

end PerronFrobeniusFin1

namespace PerronFrobeniusFin2

open FusionRing

noncomputable section

/-- Discriminant of the characteristic polynomial of a 2×2 matrix,
`(M₀₀ - M₁₁)² + 4 M₀₁ M₁₀`. -/
def pfDiscriminant (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0

/-- The larger root of the characteristic polynomial of a 2×2 matrix,
the candidate Perron–Frobenius eigenvalue. -/
def pfEigenvalue (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (M 0 0 + M 1 1 + Real.sqrt (pfDiscriminant M)) / 2

/-- Explicit Perron–Frobenius eigenvector of a 2×2 matrix,
`(M 0 1, pfEigenvalue M - M 0 0)`. -/
def pfEigenvec (M : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → ℝ :=
  ![M 0 1, pfEigenvalue M - M 0 0]

/-- The discriminant `pfDiscriminant M` of a strictly positive 2×2
matrix is positive. -/
lemma pfDiscriminant_pos (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    0 < pfDiscriminant M := by
  unfold pfDiscriminant
  nlinarith [sq_nonneg (M 0 0 - M 1 1), hM 0 1, hM 1 0]

/-- The Perron–Frobenius eigenvalue of a strictly positive 2×2 matrix
is positive. -/
lemma pfEigenvalue_pos (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    0 < pfEigenvalue M := by
  unfold pfEigenvalue
  linarith [pfDiscriminant_pos M hM |> Real.sqrt_pos_of_pos, hM 0 0, hM 1 1]

/-- For a strictly positive 2×2 matrix,
`M 0 0 - M 1 1 < sqrt(pfDiscriminant M)`. -/
lemma sqrt_disc_gt_diff (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    M 0 0 - M 1 1 < Real.sqrt (pfDiscriminant M) := by
  have hΔ := pfDiscriminant_pos M hM
  have hΔ_ge : (M 0 0 - M 1 1) ^ 2 < pfDiscriminant M := by
    unfold pfDiscriminant; nlinarith [hM 0 1, hM 1 0]
  by_cases h : 0 ≤ M 0 0 - M 1 1
  · calc M 0 0 - M 1 1 = Real.sqrt ((M 0 0 - M 1 1) ^ 2) := (Real.sqrt_sq h).symm
      _ < Real.sqrt (pfDiscriminant M) := Real.sqrt_lt_sqrt (sq_nonneg _) hΔ_ge
  · linarith [Real.sqrt_pos_of_pos hΔ]

/-- The explicit eigenvector `pfEigenvec M` has strictly positive
entries when `M` does. -/
lemma pfEigenvec_pos (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    ∀ i, 0 < pfEigenvec M i := by
  intro i; fin_cases i
  · show 0 < (pfEigenvec M) 0
    simp [pfEigenvec, Matrix.cons_val_zero]; exact hM 0 1
  · show 0 < (pfEigenvec M) 1
    simp [pfEigenvec, Matrix.cons_val_one]
    unfold pfEigenvalue; linarith [sqrt_disc_gt_diff M hM]

/-- `pfEigenvalue M` is a root of the characteristic polynomial of `M`. -/
lemma pfEigenvalue_char_poly (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    pfEigenvalue M ^ 2 - (M 0 0 + M 1 1) * pfEigenvalue M +
    (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 0 := by
  unfold pfEigenvalue pfDiscriminant
  have hΔ : 0 ≤ pfDiscriminant M := le_of_lt (pfDiscriminant_pos M hM)
  unfold pfDiscriminant at hΔ
  nlinarith [Real.sq_sqrt hΔ]

/-- `pfEigenvec M` is an eigenvector of `M` with eigenvalue
`pfEigenvalue M`. -/
lemma pfEigenvec_is_eigenvec (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    M.mulVec (pfEigenvec M) = pfEigenvalue M • pfEigenvec M := by
  ext i; fin_cases i
  ·
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pfEigenvec,
          Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]; ring
  ·
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pfEigenvec,
          Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
    nlinarith [pfEigenvalue_char_poly M hM]

/-- Uniqueness of positive eigenvectors of a strictly positive 2×2
matrix up to scaling. -/
lemma pfUnique_fin2 (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j)
    (r₁ r₂ : ℝ) (v w : Fin 2 → ℝ)
    (hv : ∀ i, 0 < v i) (hev : M.mulVec v = r₁ • v)
    (hw : ∀ i, 0 < w i) (hew : M.mulVec w = r₂ • w) :
    ∃ c : ℝ, ∀ i, w i = c * v i := by
  have hv0 := hv 0; have hv1 := hv 1; have hw0 := hw 0; have hw1 := hw 1
  have hv0_ne : v 0 ≠ 0 := ne_of_gt hv0
  have hv1_ne : v 1 ≠ 0 := ne_of_gt hv1
  have hw0_ne : w 0 ≠ 0 := ne_of_gt hw0
  have hw1_ne : w 1 ≠ 0 := ne_of_gt hw1

  have hrv0 : M 0 0 * v 0 + M 0 1 * v 1 = r₁ * v 0 := by
    have := congr_fun hev 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hrv1 : M 1 0 * v 0 + M 1 1 * v 1 = r₁ * v 1 := by
    have := congr_fun hev 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hrw0 : M 0 0 * w 0 + M 0 1 * w 1 = r₂ * w 0 := by
    have := congr_fun hew 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hrw1 : M 1 0 * w 0 + M 1 1 * w 1 = r₂ * w 1 := by
    have := congr_fun hew 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    linarith

  have hv_01 : (r₁ - M 0 0) * v 0 = M 0 1 * v 1 := by linarith
  have hv_10 : (r₁ - M 1 1) * v 1 = M 1 0 * v 0 := by linarith
  have hw_01 : (r₂ - M 0 0) * w 0 = M 0 1 * w 1 := by linarith

  have hr1_gt0 : M 0 0 < r₁ := by nlinarith [hM 0 1]
  have hr1_gt1 : M 1 1 < r₁ := by nlinarith [hM 1 0]
  have hr2_gt0 : M 0 0 < r₂ := by nlinarith [hM 0 1]
  have hr2_gt1 : M 1 1 < r₂ := by nlinarith [hM 1 0]

  have hcp1 : (r₁ - M 0 0) * (r₁ - M 1 1) = M 0 1 * M 1 0 := by
    have ha : r₁ - M 0 0 = M 0 1 * v 1 / v 0 := by field_simp; linarith
    have hd : r₁ - M 1 1 = M 1 0 * v 0 / v 1 := by field_simp; linarith
    rw [ha, hd]; field_simp
  have hcp2 : (r₂ - M 0 0) * (r₂ - M 1 1) = M 0 1 * M 1 0 := by
    have ha : r₂ - M 0 0 = M 0 1 * w 1 / w 0 := by field_simp; linarith
    have hd : r₂ - M 1 1 = M 1 0 * w 0 / w 1 := by field_simp; linarith
    rw [ha, hd]; field_simp

  have hfact : (r₁ - r₂) * (r₁ + r₂ - (M 0 0 + M 1 1)) = 0 := by nlinarith

  have hr_eq : r₁ = r₂ := by
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · exfalso; linarith

  rw [hr_eq] at hv_01

  have h_rne : r₂ - M 0 0 ≠ 0 := by linarith
  have hcross_eq : (r₂ - M 0 0) * (v 0 * w 1 - w 0 * v 1) = 0 := by
    have l1 : (r₂ - M 0 0) * v 0 * w 1 = M 0 1 * v 1 * w 1 := by
      have := congr_arg (· * w 1) hv_01; simp [mul_assoc] at this; linarith
    have l2 : (r₂ - M 0 0) * w 0 * v 1 = M 0 1 * w 1 * v 1 := by
      have := congr_arg (· * v 1) hw_01; simp [mul_assoc] at this; linarith
    linarith [mul_comm (v 1) (w 1)]

  have hcross : v 0 * w 1 = w 0 * v 1 := by
    rcases mul_eq_zero.mp hcross_eq with h | h
    · exact absurd h h_rne
    · linarith

  refine ⟨w 0 / v 0, ?_⟩
  intro i; fin_cases i
  · show w 0 = w 0 / v 0 * v 0
    rw [div_mul_cancel₀ _ hv0_ne]
  · show w 1 = w 0 / v 0 * v 1
    rw [div_mul_eq_mul_div, ← hcross, mul_div_cancel_left₀ _ hv0_ne]

end

noncomputable instance : HasPerronFrobeniusProperty (Fin 2) where
  pfEigenvec := fun M hM =>
    ⟨pfEigenvalue M, pfEigenvec M,
     pfEigenvalue_pos M hM, pfEigenvec_pos M hM, pfEigenvec_is_eigenvec M hM⟩
  pfUnique := fun M hM r₁ r₂ v w hv hev hw hew =>
    pfUnique_fin2 M hM r₁ r₂ v w hv hev hw hew

end PerronFrobeniusFin2

/-- Existence of a Perron–Frobenius eigenpair for any strictly positive
matrix: a positive eigenvalue `r` together with a strictly positive
eigenvector. -/
noncomputable def perronFrobeniusExistence {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    Σ' (r : ℝ) (v : ι → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ M.mulVec v = r • v :=
  PerronFrobenius.perronFrobeniusExistence M hM

/-- General `HasPerronFrobeniusProperty` instance combining the existence
result `perronFrobeniusExistence` with the uniqueness
`PerronFrobeniusGeneral.pfUnique_general`. -/
noncomputable instance instHasPerronFrobeniusPropertyGeneral
    (ι : Type*) [DecidableEq ι] [Fintype ι] [Nonempty ι] :
    FusionRing.HasPerronFrobeniusProperty ι where
  pfEigenvec := fun M hM => perronFrobeniusExistence M hM
  pfUnique := fun M hM r₁ r₂ v w hv hev hw hew =>
    PerronFrobeniusGeneral.pfUnique_general M hM r₁ r₂ v w hv hev hw hew

section VerifyInstance

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]

end VerifyInstance

/-- Existence part of EGNO Theorem 1.44.1: every strictly positive
matrix has a positive eigenvalue with a positive eigenvector. -/
noncomputable def theorem_1_44_1_existence
    {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    Σ' (r : ℝ) (v : ι → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ M.mulVec v = r • v :=
  perronFrobeniusExistence M hM

/-- Uniqueness part of EGNO Theorem 1.44.1: any two positive
eigenvectors of a strictly positive matrix are scalar multiples
of each other. -/
theorem theorem_1_44_1_uniqueness
    {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j)
    (r₁ r₂ : ℝ) (v w : ι → ℝ)
    (hv : ∀ i, 0 < v i) (hev : M.mulVec v = r₁ • v)
    (hw : ∀ i, 0 < w i) (hew : M.mulVec w = r₂ • w) :
    ∃ c : ℝ, ∀ i, w i = c * v i :=
  PerronFrobeniusGeneral.pfUnique_general M hM r₁ r₂ v w hv hev hw hew

/-- EGNO Theorem 1.44.1 (Perron–Frobenius for strictly positive
matrices): existence and uniqueness of a Perron–Frobenius eigenpair,
bundled as a `PerronFrobenius M`. -/
noncomputable def theorem_1_44_1
    {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    FusionRing.PerronFrobenius M :=
  let ⟨r, v, hr_pos, hv_pos, hv_eig⟩ := theorem_1_44_1_existence M hM
  { ev := r
    evec := v
    ev_pos := hr_pos
    evec_pos := hv_pos
    is_eigenvec := hv_eig
    unique := fun μ w hw_pos hw_eig =>
      theorem_1_44_1_uniqueness M hM r μ v w hv_pos hv_eig hw_pos hw_eig }

open FusionRing

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable (R : FusionRing ι)


namespace FPdimData

variable {R}
variable (fpd : R.FPdimData)


end FPdimData

end FusionRing

/-- Top-level statement of EGNO Proposition 1.45.4 packaged as a single
theorem on `R.FPdimData`. -/
theorem proposition_1_45_4 {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    {R : FusionRing ι} (fpd : R.FPdimData) (i : ι) :
    IsIntegral ℤ (fpd.d i) ∧
    (∀ μ : ℂ, FusionRing.IsComplexEigenvalue (R.leftMulMatrixR i) μ → ‖μ‖ ≤ fpd.d i) ∧
    fpd.d i ≥ 1 :=
  fpd.proposition_1_45_4 i
