/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Topology.Connected.Basic

noncomputable section

open Matrix Finset BigOperators

structure HypersurfacePatch (n : ℕ) where
  domain : Set (Fin n → ℝ)
  domain_open : IsOpen domain
  f : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  smooth : ContDiffOn ℝ ⊤ f domain
  immersion : ∀ x ∈ domain, Function.Injective (fderiv ℝ f x)

variable {n : ℕ}

def HypersurfacePatch.partialDeriv (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i : Fin n) : Fin (n + 1) → ℝ :=
  fderiv ℝ patch.f x (Pi.single i 1)

def generalizedCross {n : ℕ} (v : Fin n → (Fin (n + 1) → ℝ)) :
    Fin (n + 1) → ℝ :=
  fun j => (-1 : ℝ) ^ (j : ℕ) * (Matrix.of (fun (i : Fin n) (k : Fin n) =>
    v i (Fin.succAbove j k))).det

def orientationMatrix (patch : HypersurfacePatch n) (x : Fin n → ℝ)
    (w : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun (row : Fin (n + 1)) (col : Fin (n + 1)) =>
    if h : col.val < n then
      patch.partialDeriv x ⟨col.val, h⟩ row
    else
      w row

def gaussNormal (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  let crossVec := generalizedCross (patch.partialDeriv x)
  let nrm := Real.sqrt (crossVec ⬝ᵥ crossVec)
  fun j => crossVec j / nrm

noncomputable def firstFundamentalForm (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let Df := fun i => fderiv ℝ patch.f x (Pi.single i 1)
  Matrix.of (fun i j => (Df i) ⬝ᵥ (Df j))

noncomputable def jacobianMatrix (patch : HypersurfacePatch n) (x : Fin n → ℝ) :
    Matrix (Fin (n + 1)) (Fin n) ℝ :=
  Matrix.of (fun k i => fderiv ℝ patch.f x (Pi.single i 1) k)

lemma firstFundamentalForm_eq_conjTranspose_mul (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) :
    firstFundamentalForm patch x = (jacobianMatrix patch x)ᴴ * (jacobianMatrix patch x) := by
  ext i j
  simp [firstFundamentalForm, jacobianMatrix, mul_apply, of_apply, dotProduct]

lemma jacobian_mulVec_eq_fderiv (patch : HypersurfacePatch n) (x v : Fin n → ℝ) :
    jacobianMatrix patch x *ᵥ v = fderiv ℝ patch.f x v := by
  ext k
  simp only [jacobianMatrix, mulVec, dotProduct, of_apply]
  have hv : v = ∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Finset.mem_univ]
  conv_rhs => rw [hv, map_sum]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem firstFundamentalForm_posDef (patch : HypersurfacePatch n) (x : Fin n → ℝ)
    (hx : x ∈ patch.domain) :
    (firstFundamentalForm patch x).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos
  · rw [firstFundamentalForm_eq_conjTranspose_mul]
    exact isHermitian_conjTranspose_mul_self _
  · intro v hv
    rw [firstFundamentalForm_eq_conjTranspose_mul, ← mulVec_mulVec,
        dotProduct_mulVec, vecMul_conjTranspose, star_star]
    rw [dotProduct_star_self_pos_iff, jacobian_mulVec_eq_fderiv]
    intro h
    exact hv (patch.immersion x hx (h.trans (map_zero _).symm))

end







noncomputable def secondFundamentalForm {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j =>
    (fderiv ℝ (fderiv ℝ patch.f · (Pi.single j 1)) x (Pi.single i 1)) ⬝ᵥ
    (gaussNormal patch x))

open Matrix in
theorem secondFundamentalForm_symmetric {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i j : Fin n) :
    secondFundamentalForm patch x i j = secondFundamentalForm patch x j i := by
  simp only [secondFundamentalForm, of_apply]
  congr 1
  have hfat : ContDiffAt ℝ ⊤ patch.f x :=
    patch.smooth.contDiffAt (patch.domain_open.mem_nhds hx)
  have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ patch.f) x :=
    (hfat.fderiv_right (m := ⊤) le_top).differentiableAt (by exact WithTop.top_ne_zero)
  have hconn : ∀ (v w : Fin n → ℝ),
      fderiv ℝ (fun y => fderiv ℝ patch.f y v) x w = (fderiv ℝ (fderiv ℝ patch.f) x w) v := by
    intro v w
    have hcomp : (fun y => fderiv ℝ patch.f y v) =
        (ContinuousLinearMap.apply ℝ (Fin (n + 1) → ℝ) v) ∘ (fderiv ℝ patch.f) := by
      ext y; simp [ContinuousLinearMap.apply_apply]
    rw [hcomp, fderiv_comp x]
    · simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    · exact (ContinuousLinearMap.apply ℝ (Fin (n + 1) → ℝ) v).differentiableAt
    · exact hfderiv_diff
  rw [hconn, hconn]
  exact (hfat.isSymmSndFDerivAt_of_omega).eq (Pi.single i 1) (Pi.single j 1)

noncomputable def shapeOperator {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (firstFundamentalForm patch x)⁻¹ * (secondFundamentalForm patch x)

open Matrix in
def IsPrincipalCurvature {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (κ : ℝ) : Prop :=
  (shapeOperator patch x).charpoly.IsRoot κ

lemma dotProduct_sum_smul {m k : ℕ} (v : Fin k → (Fin m → ℝ)) (a : Fin k → ℝ) (w : Fin m → ℝ) :
    (∑ j, a j • v j) ⬝ᵥ w = ∑ j, a j * (v j ⬝ᵥ w) := by
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext k
  rw [Finset.mul_sum]
  congr 1; ext i; ring






noncomputable def meanCurvature {n : ℕ} (patch : HypersurfacePatch n) (x : Fin n → ℝ) : ℝ :=
  (shapeOperator patch x).trace

noncomputable def gaussCurvature {n : ℕ} (patch : HypersurfacePatch n) (x : Fin n → ℝ) : ℝ :=
  (shapeOperator patch x).det

noncomputable def scalarCurvature {n : ℕ} (patch : HypersurfacePatch n) (x : Fin n → ℝ) : ℝ :=
  ((shapeOperator patch x).trace ^ 2 - ((shapeOperator patch x) * (shapeOperator patch x)).trace) / 2


noncomputable section

open Matrix Finset BigOperators

def coordinateJacobian {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ φ x (Pi.single j 1) i

lemma generalizedCross_linear_combination {n : ℕ}
    (v : Fin n → (Fin (n + 1) → ℝ)) (A : Matrix (Fin n) (Fin n) ℝ) :
    generalizedCross (fun i => ∑ j : Fin n, A j i • v j) =
    A.det • generalizedCross v := by
  ext j
  simp only [generalizedCross, Pi.smul_apply, smul_eq_mul]
  ring_nf
  congr 1
  have h : (Matrix.of (fun (i : Fin n) (k : Fin n) =>
      (∑ l : Fin n, A l i • v l) (Fin.succAbove j k))) =
      A.transpose * (Matrix.of (fun (i : Fin n) (k : Fin n) => v i (Fin.succAbove j k))) := by
    ext i k
    simp [mul_apply, transpose_apply, of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h, det_mul, det_transpose]

theorem gaussNormal_coordinate_change {n : ℕ}
    (patch tildeP : HypersurfacePatch n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (h_eq : tildeP.f = patch.f ∘ φ)
    (hφ : DifferentiableAt ℝ φ x)
    (hf : DifferentiableAt ℝ patch.f (φ x))
    (hdet_pos : (coordinateJacobian φ x).det > 0) :
    gaussNormal tildeP x = gaussNormal patch (φ x) := by
  have hchain : fderiv ℝ tildeP.f x = (fderiv ℝ patch.f (φ x)).comp (fderiv ℝ φ x) := by
    conv_lhs => rw [h_eq]; exact fderiv_comp x hf hφ
  have hpartials : (fun i => fderiv ℝ tildeP.f x (Pi.single i 1)) =
      (fun i => ∑ k : Fin n, (coordinateJacobian φ x) k i •
        fderiv ℝ patch.f (φ x) (Pi.single k 1)) := by
    ext i
    rw [hchain, ContinuousLinearMap.comp_apply]
    have : (fderiv ℝ φ x (Pi.single i 1) : Fin n → ℝ) =
        ∑ k : Fin n, (fderiv ℝ φ x (Pi.single i 1) k) •
          (Pi.single k (1 : ℝ) : Fin n → ℝ) := by
      ext p; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [this, map_sum]
    simp only [ContinuousLinearMap.map_smul, coordinateJacobian, of_apply]
  have hpartials2 : tildeP.partialDeriv x =
      (fun i => ∑ k : Fin n, (coordinateJacobian φ x) k i •
        patch.partialDeriv (φ x) k) := by
    unfold HypersurfacePatch.partialDeriv
    exact hpartials
  unfold gaussNormal
  rw [hpartials2, generalizedCross_linear_combination]
  ext j
  simp only [Pi.smul_apply, smul_eq_mul, dotProduct]
  have h1 : ∑ i, (coordinateJacobian φ x).det *
      (generalizedCross (patch.partialDeriv (φ x))) i *
      ((coordinateJacobian φ x).det *
      (generalizedCross (patch.partialDeriv (φ x))) i) =
      (coordinateJacobian φ x).det ^ 2 * ∑ i,
      (generalizedCross (patch.partialDeriv (φ x))) i *
      (generalizedCross (patch.partialDeriv (φ x))) i := by
    rw [Finset.mul_sum]; congr 1; ext i; ring
  rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hdet_pos)]
  field_simp

theorem firstFundamentalForm_coordinate_change {n : ℕ}
    (patch tildeP : HypersurfacePatch n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (h_eq : tildeP.f = patch.f ∘ φ)
    (hφ : DifferentiableAt ℝ φ x)
    (hf : DifferentiableAt ℝ patch.f (φ x)) :
    firstFundamentalForm tildeP x =
    (coordinateJacobian φ x).transpose * firstFundamentalForm patch (φ x) *
      (coordinateJacobian φ x) := by
  have hchain : fderiv ℝ tildeP.f x = (fderiv ℝ patch.f (φ x)).comp (fderiv ℝ φ x) := by
    conv_lhs => rw [h_eq]; exact fderiv_comp x hf hφ
  have expand : ∀ m : Fin n, fderiv ℝ tildeP.f x (Pi.single m 1) =
      ∑ k : Fin n, (fderiv ℝ φ x (Pi.single m 1) k) •
        fderiv ℝ patch.f (φ x) (Pi.single k 1) := by
    intro m
    have h1 : fderiv ℝ tildeP.f x (Pi.single m 1) =
        fderiv ℝ patch.f (φ x) (fderiv ℝ φ x (Pi.single m 1)) := by
      rw [hchain]; rfl
    rw [h1]
    have h2 : (fderiv ℝ φ x (Pi.single m 1) : Fin n → ℝ) =
        ∑ k : Fin n, (fderiv ℝ φ x (Pi.single m 1) k) •
          (Pi.single k (1 : ℝ) : Fin n → ℝ) := by
      ext p; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    conv_lhs => rw [h2]
    rw [map_sum]
    simp only [ContinuousLinearMap.map_smul]
  ext i j
  simp only [firstFundamentalForm, of_apply, mul_apply, transpose_apply,
             coordinateJacobian, dotProduct, Finset.sum_mul]
  rw [expand i, expand j]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext l
  rw [Finset.sum_comm]
  congr 1; ext k
  congr 1; ext p
  ring

theorem secondFundamentalForm_coordinate_change_of_entries {n : ℕ}
    (patch tildeP : HypersurfacePatch n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (h_chain : ∀ i j : Fin n, secondFundamentalForm tildeP x i j =
      ∑ k, ∑ l, (coordinateJacobian φ x) k i *
        secondFundamentalForm patch (φ x) k l *
        (coordinateJacobian φ x) l j) :
    secondFundamentalForm tildeP x =
    (coordinateJacobian φ x).transpose * secondFundamentalForm patch (φ x) *
      (coordinateJacobian φ x) := by
  ext i j
  rw [h_chain]
  simp only [mul_apply, transpose_apply, coordinateJacobian, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]




theorem shapeOperator_coordinate_change {n : ℕ}
    (patch tildeP : HypersurfacePatch n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (hG : firstFundamentalForm tildeP x =
      (coordinateJacobian φ x).transpose * firstFundamentalForm patch (φ x) *
        (coordinateJacobian φ x))
    (hH : secondFundamentalForm tildeP x =
      (coordinateJacobian φ x).transpose * secondFundamentalForm patch (φ x) *
        (coordinateJacobian φ x))
    (hφ_det : IsUnit (coordinateJacobian φ x).det)
    (hG_det : IsUnit (firstFundamentalForm patch (φ x)).det) :
    shapeOperator tildeP x =
    (coordinateJacobian φ x)⁻¹ * shapeOperator patch (φ x) * (coordinateJacobian φ x) := by
  unfold shapeOperator
  rw [hG, hH]
  set Dφ := coordinateJacobian φ x
  set G := firstFundamentalForm patch (φ x)
  set H := secondFundamentalForm patch (φ x)
  have hAt : IsUnit Dφ.transpose.det := by rw [det_transpose]; exact hφ_det
  have hAtBA : IsUnit (Dφ.transpose * G * Dφ).det := by
    rw [det_mul, det_mul, det_transpose]; exact (hφ_det.mul hG_det).mul hφ_det
  have h : Dφ.transpose * G * Dφ * (Dφ⁻¹ * (G⁻¹ * H) * Dφ) = Dφ.transpose * H * Dφ := by
    have : Dφ.transpose * G * Dφ * (Dφ⁻¹ * (G⁻¹ * H) * Dφ) =
        Dφ.transpose * G * (Dφ * Dφ⁻¹) * (G⁻¹ * H) * Dφ := by
      simp only [mul_assoc]
    rw [this, mul_nonsing_inv _ hφ_det]
    simp only [mul_one, mul_assoc]
    rw [← mul_assoc G G⁻¹, mul_nonsing_inv _ hG_det, one_mul]
  have key := congr_arg ((Dφ.transpose * G * Dφ)⁻¹ * ·) h
  simp only at key
  rw [nonsing_inv_mul_cancel_left _ _ hAtBA] at key
  exact key.symm


end

noncomputable section

open Matrix Finset BigOperators

def normalDerivMatrix {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun (row : Fin (n + 1)) (col : Fin (n + 1)) =>
    if h : col.val < n then
      fderiv ℝ (gaussNormal patch) x (Pi.single ⟨col.val, h⟩ 1) row
    else
      gaussNormal patch x row

end

noncomputable section

open Matrix Finset BigOperators

lemma firstFundamentalForm_eq_transpose_mul {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) :
    firstFundamentalForm patch x =
    (jacobianMatrix patch x).transpose * (jacobianMatrix patch x) := by
  have h := firstFundamentalForm_eq_conjTranspose_mul patch x
  rwa [conjTranspose_eq_transpose_of_trivial] at h



end

noncomputable section

open Matrix Finset BigOperators

lemma dotProduct_self_eq_one_of_sqrt_eq_one {n : ℕ} (ν : Fin (n + 1) → ℝ)
    (h : Real.sqrt (ν ⬝ᵥ ν) = 1) : ν ⬝ᵥ ν = 1 := by
  have hnn : (0 : ℝ) ≤ ν ⬝ᵥ ν := by
    simp only [dotProduct]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (ν i))
  nlinarith [Real.sq_sqrt hnn]



lemma det_gram_eq_cross_dotProduct_self (v : Fin 2 → (Fin 3 → ℝ)) :
    (Matrix.of (fun i j : Fin 2 => (v i) ⬝ᵥ (v j))).det =
    (generalizedCross v) ⬝ᵥ (generalizedCross v) := by
  have hc : generalizedCross v = ![v 0 1 * v 1 2 - v 0 2 * v 1 1,
                                     -(v 0 0 * v 1 2 - v 0 2 * v 1 0),
                                     v 0 0 * v 1 1 - v 0 1 * v 1 0] := by
    ext j
    fin_cases j <;> simp [generalizedCross, det_fin_two, of_apply, Fin.succAbove,
      Fin.castSucc, Fin.succ, Fin.lt_def]
  rw [hc]
  simp [det_fin_two, of_apply, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end

noncomputable section

open Matrix Finset BigOperators

def shapeOperatorLinkingMatrix {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun (row col : Fin (n + 1)) =>
    if hr : row.val < n then
      if hc : col.val < n then
        -(shapeOperator patch x ⟨row.val, hr⟩ ⟨col.val, hc⟩)
      else 0
    else
      if _hc : col.val < n then 0 else 1

lemma shapeOperatorLinkingMatrix_det {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) :
    (shapeOperatorLinkingMatrix patch x).det =
    (-1 : ℝ) ^ n * (shapeOperator patch x).det := by
  have heq : shapeOperatorLinkingMatrix patch x =
    ((Matrix.reindex finSumFinEquiv finSumFinEquiv)
      (Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))) := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [shapeOperatorLinkingMatrix, of_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    by_cases hin : i < n <;> by_cases hjn : j < n
    · simp only [hin, hjn, dite_true]
      show -(shapeOperator patch x) ⟨i, hin⟩ ⟨j, hjn⟩ =
        Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 1
          (finSumFinEquiv.symm ⟨i, hi⟩) (finSumFinEquiv.symm ⟨j, hj⟩)
      simp [finSumFinEquiv, Fin.addCases, hin, hjn, Fin.castLT, Matrix.fromBlocks]
    · simp only [hin, hjn, dite_true, dite_false]
      show (0 : ℝ) = Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 1
        (finSumFinEquiv.symm ⟨i, hi⟩) (finSumFinEquiv.symm ⟨j, hj⟩)
      simp [finSumFinEquiv, Fin.addCases, hin, hjn, Fin.castLT, Fin.subNat, Matrix.fromBlocks]
    · simp only [hin, hjn, dite_false, dite_true]
      show (0 : ℝ) = Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 1
        (finSumFinEquiv.symm ⟨i, hi⟩) (finSumFinEquiv.symm ⟨j, hj⟩)
      simp [finSumFinEquiv, Fin.addCases, hin, hjn, Fin.castLT, Fin.subNat, Matrix.fromBlocks]
    · simp only [hin, hjn, dite_false]
      show (1 : ℝ) = Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 1
        (finSumFinEquiv.symm ⟨i, hi⟩) (finSumFinEquiv.symm ⟨j, hj⟩)
      simp [finSumFinEquiv, Fin.addCases, hin, hjn, Fin.castLT, Fin.subNat,
        Matrix.fromBlocks, Matrix.one_apply]
      omega
  rw [heq, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg,
    Fintype.card_fin, Matrix.det_one, mul_one]




end

def IsCompactHypersurface {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1)))) : Prop :=
  IsCompact M
