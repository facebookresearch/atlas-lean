/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Hausdorff

noncomputable section

open scoped Matrix

namespace GaussMapDegree

def gramMatrix (n : ℕ) (σ : (Fin n → ℝ) → (Fin (n + 1) → ℝ))
    (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let Dσ := fderiv ℝ σ u
  fun i j =>
    ∑ k : Fin (n + 1), Dσ (Function.update 0 i 1) k * Dσ (Function.update 0 j 1) k

def augmentedMatrix {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin n) ℝ)
    (ν : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if h : (j : ℕ) < n then B i ⟨j, h⟩
    else ν i

structure SmoothHypersurfaceMap (n : ℕ) where
  domainU : Set (Fin n → ℝ)
  domainU_open : IsOpen domainU
  domainV : Set (Fin n → ℝ)
  domainV_open : IsOpen domainV
  σ : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  τ : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  σ_smooth : ContDiffOn ℝ ⊤ σ domainU
  σ_immersion : ∀ u ∈ domainU, Function.Injective (fderiv ℝ σ u)
  τ_smooth : ContDiffOn ℝ ⊤ τ domainV
  τ_immersion : ∀ v ∈ domainV, Function.Injective (fderiv ℝ τ v)
  h : (Fin n → ℝ) → (Fin n → ℝ)
  h_maps : ∀ u ∈ domainU, h u ∈ domainV
  h_smooth : ContDiffOn ℝ ⊤ h domainU
  chain_rule : ∀ u ∈ domainU,
    (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => fderiv ℝ σ u (Function.update 0 j 1) i) *
      (Matrix.of fun (i : Fin n) (j : Fin n) => fderiv ℝ h u (Function.update 0 j 1) i) =
    (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => fderiv ℝ (τ ∘ h) u (Function.update 0 j 1) i)
  ν : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  ν_tilde : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  ν_orth : ∀ u ∈ domainU, ∀ j : Fin n,
    ∑ i : Fin (n + 1), fderiv ℝ σ u (Function.update 0 j 1) i * ν u i = 0
  ν_norm : ∀ u ∈ domainU, ∑ i : Fin (n + 1), ν u i ^ 2 = 1
  ν_tilde_orth : ∀ v ∈ domainV, ∀ j : Fin n,
    ∑ i : Fin (n + 1), fderiv ℝ τ v (Function.update 0 j 1) i * ν_tilde v i = 0
  ν_tilde_norm : ∀ v ∈ domainV, ∑ i : Fin (n + 1), ν_tilde v i ^ 2 = 1
  σ_pos_oriented : ∀ u ∈ domainU,
    0 < (augmentedMatrix (fun i j => fderiv ℝ σ u (Function.update 0 j 1) i)
      (ν u)).det
  τ_pos_oriented : ∀ v ∈ domainV,
    0 < (augmentedMatrix (fun i j => fderiv ℝ τ v (Function.update 0 j 1) i)
      (ν_tilde v)).det

def SmoothHypersurfaceMap.jacobianMatrix {n : ℕ} (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ Φ.h u (Function.update 0 j 1) i

def SmoothHypersurfaceMap.jacobianDet {n : ℕ} (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ) : ℝ :=
  (Φ.jacobianMatrix u).det

theorem det_augmented_eq_det_mul {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin (n + 1)) (Fin n) ℝ)
    (ν : Fin (n + 1) → ℝ) :
    (augmentedMatrix (A * H) ν).det =
      H.det * (augmentedMatrix A ν).det := by

  set T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j =>
    if hi : (i : ℕ) < n then
      if hj : (j : ℕ) < n then H ⟨i, hi⟩ ⟨j, hj⟩
      else 0
    else
      if (j : ℕ) < n then 0 else 1

  suffices factored : augmentedMatrix (A * H) ν = augmentedMatrix A ν * T by
    rw [factored, Matrix.det_mul]

    suffices hT : T.det = H.det by rw [hT, mul_comm]


    rw [Matrix.det_succ_column T (Fin.last n)]

    have hcol : ∀ i : Fin (n + 1), i ≠ Fin.last n →
        T i (Fin.last n) = 0 := by
      intro i hi
      simp only [T, Matrix.of_apply]
      have hi' : (i : ℕ) < n := by
        have := i.isLt; simp [Fin.ext_iff, Fin.val_last] at hi; omega
      simp [hi']
    have hTlast : T (Fin.last n) (Fin.last n) = 1 := by
      simp [T, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp only [Fin.val_last, hTlast]
      have : (-1 : ℝ) ^ (n + n) = 1 := by
        have : Even (n + n) := ⟨n, by ring⟩
        exact Even.neg_one_pow this
      simp only [this, one_mul, mul_one]
      congr 1
      ext a b
      simp [Matrix.submatrix, T, Matrix.of_apply, Fin.succAbove]

    · intro i _ hi
      simp [hcol i hi]
    · intro h
      exact absurd (Finset.mem_univ _) h


  ext i j
  simp only [augmentedMatrix, Matrix.of_apply, Matrix.mul_apply, T]
  split_ifs with hj
  ·

    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.lt_irrefl,
      dite_false, mul_zero, add_zero]
    congr 1
    ext k
    have hk : (k : ℕ) < n := k.isLt
    simp only [dif_pos hk]
  ·

    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.lt_irrefl,
      dite_false, mul_one]


    convert (zero_add (ν i)).symm using 1
    congr 1
    apply Finset.sum_eq_zero
    intro k _
    simp

theorem det_jacobian_formula {n : ℕ}
    (Df : Matrix (Fin (n + 1)) (Fin n) ℝ)
    (Dφf : Matrix (Fin (n + 1)) (Fin n) ℝ)
    (ν_tilde : Fin (n + 1) → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hchain : Df * H = Dφf)
    (hG_pos : 0 < (augmentedMatrix Df ν_tilde).det)
    (hG_sq : (augmentedMatrix Df ν_tilde).det ^ 2 = (Dfᵀ * Df).det) :
    H.det = (augmentedMatrix Dφf ν_tilde).det /
      Real.sqrt ((Dfᵀ * Df).det) := by
  have hdet_aug := det_augmented_eq_det_mul H Df ν_tilde
  rw [hchain] at hdet_aug
  have hG_ne_zero : (augmentedMatrix Df ν_tilde).det ≠ 0 := ne_of_gt hG_pos
  have hG_nonneg : (0 : ℝ) ≤ (augmentedMatrix Df ν_tilde).det := le_of_lt hG_pos
  have hG_eq_sqrt : (augmentedMatrix Df ν_tilde).det = Real.sqrt ((Dfᵀ * Df).det) := by
    rw [← hG_sq, Real.sqrt_sq hG_nonneg]
  rw [hdet_aug, hG_eq_sqrt, mul_div_cancel_right₀ _ (ne_of_gt (by rwa [← hG_eq_sqrt]))]

def SmoothHypersurfaceMap.sourceJacobian {n : ℕ} (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin n) ℝ :=
  fun i j => fderiv ℝ Φ.σ u (Function.update 0 j 1) i

def SmoothHypersurfaceMap.composedJacobian {n : ℕ} (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin n) ℝ :=
  fun i j => fderiv ℝ (Φ.τ ∘ Φ.h) u (Function.update 0 j 1) i

theorem SmoothHypersurfaceMap.chain_rule_matrices {n : ℕ} (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ) (hu : u ∈ Φ.domainU) :
    Φ.sourceJacobian u * Φ.jacobianMatrix u = Φ.composedJacobian u :=
  Φ.chain_rule u hu


theorem det_augmented_sq_of_orthonormal_last_col {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin n) ℝ)
    (ν : Fin (n + 1) → ℝ)
    (horth : ∀ j : Fin n, ∑ i : Fin (n + 1), A i j * ν i = 0)
    (hnorm : ∑ i : Fin (n + 1), ν i ^ 2 = 1) :
    (augmentedMatrix A ν).det ^ 2 = (Aᵀ * A).det := by

  have h1 : (augmentedMatrix A ν).det ^ 2 =
      ((augmentedMatrix A ν)ᵀ * (augmentedMatrix A ν)).det := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    ring
  rw [h1]

  set M := augmentedMatrix A ν
  set P := Mᵀ * M

  have hdet_sub : P.det =
      (P.submatrix finSumFinEquiv finSumFinEquiv).det :=
    (Matrix.det_submatrix_equiv_self finSumFinEquiv P).symm
  rw [hdet_sub]

  have hblock : P.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (Aᵀ * A) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext (i | i) (j | j)
    ·
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
        P, M, Matrix.mul_apply, Matrix.transpose_apply, augmentedMatrix, Matrix.of_apply]
      simp only [finSumFinEquiv_apply_left, Fin.val_castAdd]
      have hi' : (i : ℕ) < n := i.isLt
      have hj' : (j : ℕ) < n := j.isLt
      simp only [hi', hj', dite_true]
    ·
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply, P, M, Matrix.mul_apply, Matrix.transpose_apply,
        augmentedMatrix, Matrix.of_apply]
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd]
      have hi' : (i : ℕ) < n := i.isLt
      have hj_not : ¬((n + (j : ℕ)) < n) := by omega
      simp only [hi', dite_true, hj_not, dite_false]
      exact horth i
    ·
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply, P, M, Matrix.mul_apply, Matrix.transpose_apply,
        augmentedMatrix, Matrix.of_apply]
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd]
      have hi_not : ¬((n + (i : ℕ)) < n) := by omega
      have hj' : (j : ℕ) < n := j.isLt
      simp only [hi_not, dite_false, hj', dite_true]
      have := horth j
      rw [show (∑ x, ν x * A x ⟨↑j, hj'⟩) = ∑ i, A i j * ν i from
        Finset.sum_congr rfl (fun k _ => by ring)]
      exact this
    ·
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂,
        P, M, Matrix.mul_apply, Matrix.transpose_apply, augmentedMatrix, Matrix.of_apply]
      simp only [finSumFinEquiv_apply_right, Fin.val_natAdd]
      have hi_not : ¬((n + (i : ℕ)) < n) := by omega
      have hj_not : ¬((n + (j : ℕ)) < n) := by omega
      simp only [hi_not, hj_not, dite_false]
      simp only [Matrix.one_apply]
      have hij : i = j := Subsingleton.elim i j
      simp only [hij, if_true]
      rw [show (∑ x, ν x * ν x) = ∑ i, ν i ^ 2 from
        Finset.sum_congr rfl (fun k _ => by ring)]
      exact hnorm
  rw [hblock, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_jacobian_formula_geometric {n : ℕ}
    (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ)
    (ν_tilde : Fin (n + 1) → ℝ)
    (horth : ∀ j : Fin n, ∑ i : Fin (n + 1),
      (Φ.sourceJacobian u) i j * ν_tilde i = 0)
    (hnorm : ∑ i : Fin (n + 1), ν_tilde i ^ 2 = 1)
    (hpos : 0 < (augmentedMatrix (Φ.sourceJacobian u) ν_tilde).det)
    (hchain : (Φ.sourceJacobian u) * (Φ.jacobianMatrix u) =
      Φ.composedJacobian u) :
    Φ.jacobianDet u =
      (augmentedMatrix (Φ.composedJacobian u) ν_tilde).det /
        Real.sqrt ((gramMatrix n Φ.σ u).det) := by

  have hGram : gramMatrix n Φ.σ u = (Φ.sourceJacobian u)ᵀ * (Φ.sourceJacobian u) := by
    ext i j
    simp only [gramMatrix, SmoothHypersurfaceMap.sourceJacobian, Matrix.transpose_apply,
      Matrix.mul_apply]
  rw [hGram]

  have hG_sq : (augmentedMatrix (Φ.sourceJacobian u) ν_tilde).det ^ 2 =
      ((Φ.sourceJacobian u)ᵀ * (Φ.sourceJacobian u)).det :=
    det_augmented_sq_of_orthonormal_last_col (Φ.sourceJacobian u) ν_tilde horth hnorm

  exact det_jacobian_formula (Φ.sourceJacobian u) (Φ.composedJacobian u)
    ν_tilde (Φ.jacobianMatrix u) hchain hpos hG_sq

theorem det_jacobian_formula_geometric_target {n : ℕ}
    (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ)
    (htarget_orth_source : ∀ j : Fin n, ∑ i : Fin (n + 1),
      (Φ.sourceJacobian u) i j * (Φ.ν_tilde (Φ.h u)) i = 0)
    (hpos : 0 < (augmentedMatrix (Φ.sourceJacobian u) (Φ.ν_tilde (Φ.h u))).det)
    (hu : u ∈ Φ.domainU) :
    Φ.jacobianDet u =
      (augmentedMatrix (Φ.composedJacobian u) (Φ.ν_tilde (Φ.h u))).det /
        Real.sqrt ((gramMatrix n Φ.σ u).det) := by

  have hchain : (Φ.sourceJacobian u) * (Φ.jacobianMatrix u) =
      Φ.composedJacobian u := Φ.chain_rule_matrices u hu

  have hnorm : ∑ i : Fin (n + 1), (Φ.ν_tilde (Φ.h u)) i ^ 2 = 1 :=
    Φ.ν_tilde_norm (Φ.h u) (Φ.h_maps u hu)
  exact det_jacobian_formula_geometric Φ u (Φ.ν_tilde (Φ.h u))
    htarget_orth_source hnorm hpos hchain

def IsSmHypersurface (n : ℕ) (M : Set (Fin (n + 1) → ℝ)) : Prop :=
  ∀ p ∈ M, ∃ (U : Set (Fin n → ℝ)) (σ : (Fin n → ℝ) → Fin (n + 1) → ℝ),
    IsOpen U ∧ ContDiffOn ℝ ⊤ σ U ∧
    (∀ u ∈ U, Function.Injective (fderiv ℝ σ u)) ∧
    p ∈ σ '' U ∧ σ '' U ⊆ M

structure SmoothMapBetweenHypersurfaces (n : ℕ) where
  φ : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)
  φ_smooth : ContDiff ℝ ⊤ φ
  M : Set (Fin (n + 1) → ℝ)
  M_compact : IsCompact M
  M_hypersurface : IsSmHypersurface n M
  M_oriented : ∃ ν : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
    Continuous ν ∧ ∀ p ∈ M, ‖ν p‖ = 1
  M_tilde : Set (Fin (n + 1) → ℝ)
  M_tilde_compact : IsCompact M_tilde
  M_tilde_connected : IsConnected M_tilde
  M_tilde_hypersurface : IsSmHypersurface n M_tilde
  M_tilde_oriented : ∃ ν : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
    Continuous ν ∧ ∀ p ∈ M_tilde, ‖ν p‖ = 1
  φ_maps_to_target : ∀ p ∈ M, φ p ∈ M_tilde

def hypersurfaceVolume (n : ℕ) (S : Set (Fin (n + 1) → ℝ)) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure (↑n : ℝ) S).toReal

structure SmoothMapToSphere (n : ℕ) where
  φ : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)
  φ_smooth : ContDiff ℝ ⊤ φ
  M : Set (Fin (n + 1) → ℝ)
  M_compact : IsCompact M
  M_hypersurface : IsSmHypersurface n M
  M_oriented : ∃ ν : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
    Continuous ν ∧ ∀ p ∈ M, ‖ν p‖ = 1
  φ_maps_to_sphere : ∀ p ∈ M, ‖φ p‖ = 1

def sphereVolume (n : ℕ) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure (↑n : ℝ)
    {x : Fin (n + 1) → ℝ | ‖x‖ = 1}).toReal

def jacobianDetAtPoint {n : ℕ} (φ : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (σ : (Fin n → ℝ) → Fin (n + 1) → ℝ) (u : Fin n → ℝ)
    (ν_tilde : Fin (n + 1) → ℝ) : ℝ :=
  let Dφσ : Matrix (Fin (n + 1)) (Fin n) ℝ :=
    fun i j => fderiv ℝ (φ ∘ σ) u (Function.update 0 j 1) i
  (augmentedMatrix Dφσ ν_tilde).det / Real.sqrt ((gramMatrix n σ u).det)

def SmoothMapBetweenHypersurfaces.tangentMapDet {n : ℕ}
    (f : SmoothMapBetweenHypersurfaces n)
    (p : Fin (n + 1) → ℝ) : ℝ :=

  let ν_tilde := Classical.choose f.M_tilde_oriented

  let chartData := Classical.epsilon (fun (data : (Fin n → ℝ) × ((Fin n → ℝ) → Fin (n + 1) → ℝ)) =>
    let u := data.1
    let σ := data.2
    σ u = p)
  let u := chartData.1
  let σ := chartData.2
  jacobianDetAtPoint f.φ σ u (ν_tilde (f.φ p))

def degreeOfMapBetweenHypersurfacesReal {n : ℕ}
    (f : SmoothMapBetweenHypersurfaces n) : ℝ :=
  let μ := MeasureTheory.Measure.hausdorffMeasure (↑n : ℝ)
  (1 / hypersurfaceVolume n f.M_tilde) *
    ∫ p in f.M, f.tangentMapDet p ∂μ

def degreeOfMapBetweenHypersurfaces {n : ℕ}
    (f : SmoothMapBetweenHypersurfaces n) : ℤ :=
  ⌊degreeOfMapBetweenHypersurfacesReal f + 1 / 2⌋

def SmoothMapToSphere.toSmoothMapBetweenHypersurfaces {n : ℕ}
    (f : SmoothMapToSphere n)
    (sphere_hypersurface : IsSmHypersurface n {x : Fin (n + 1) → ℝ | ‖x‖ = 1})
    (sphere_connected : IsConnected {x : Fin (n + 1) → ℝ | ‖x‖ = 1})
    (sphere_compact : IsCompact {x : Fin (n + 1) → ℝ | ‖x‖ = 1})
    (sphere_oriented : ∃ ν : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
      Continuous ν ∧ ∀ p ∈ ({x : Fin (n + 1) → ℝ | ‖x‖ = 1} : Set _), ‖ν p‖ = 1) :
    SmoothMapBetweenHypersurfaces n where
  φ := f.φ
  φ_smooth := f.φ_smooth
  M := f.M
  M_compact := f.M_compact
  M_hypersurface := f.M_hypersurface
  M_oriented := f.M_oriented
  M_tilde := {x : Fin (n + 1) → ℝ | ‖x‖ = 1}
  M_tilde_compact := sphere_compact
  M_tilde_connected := sphere_connected
  M_tilde_hypersurface := sphere_hypersurface
  M_tilde_oriented := sphere_oriented
  φ_maps_to_target := fun p hp => by
    simp only [Set.mem_setOf_eq]
    exact f.φ_maps_to_sphere p hp

def SmoothMapToSphere.tangentMapDet {n : ℕ}
    (f : SmoothMapToSphere n)
    (p : Fin (n + 1) → ℝ) : ℝ :=

  let ν_tilde := f.φ p

  let chartData := Classical.epsilon (fun (data : (Fin n → ℝ) × ((Fin n → ℝ) → Fin (n + 1) → ℝ)) =>
    let u := data.1
    let σ := data.2
    σ u = p)
  let u := chartData.1
  let σ := chartData.2
  jacobianDetAtPoint f.φ σ u ν_tilde

def degreeOfMapReal {n : ℕ} (f : SmoothMapToSphere n) : ℝ :=
  let μ := MeasureTheory.Measure.hausdorffMeasure (↑n : ℝ)
  (1 / sphereVolume n) *
    ∫ p in f.M, f.tangentMapDet p ∂μ

def degreeOfMap {n : ℕ} (f : SmoothMapToSphere n) : ℤ :=
  ⌊degreeOfMapReal f + 1 / 2⌋









end GaussMapDegree
