/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_6
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory ProbabilityTheory Matrix Real Finset BigOperators

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Rigollet.Chapter4.Thm_4_10_Bridges

variable {d : ℕ}

/-- Operator (spectral) norm of a real square matrix, defined as the supremum of
$\|Av\|$ over unit vectors $v \in \mathbb{R}^d$. -/
def matOpNorm (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ (v : EuclideanSpace ℝ (Fin d)) (_ : ‖v‖ = 1),
    ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖

/-- The locally defined operator norm `matOpNorm` is definitionally equal to the
operator norm `matrixOpNorm` used in Theorem 4.6. -/
theorem matOpNorm_eq_matrixOpNorm (A : Matrix (Fin d) (Fin d) ℝ) :
    matOpNorm A = Thm_4_6.matrixOpNorm A := rfl

/-- Canonical equivalence between `Fin S.card` and the subset `S ⊆ Fin d`,
obtained from the order isomorphism that enumerates `S` in increasing order. -/
def finsetEquivFin (S : Finset (Fin d)) : Fin S.card ≃ S :=
  (Finset.orderIsoOfFin S rfl).toEquiv

/-- Restrict a random vector $X : \Omega \to \mathbb{R}^d$ to the coordinates
indexed by `S ⊆ Fin d`, viewed as a vector in $\mathbb{R}^m$ where $m = |S|$. -/
def restrictVec {Ω : Type*} (S : Finset (Fin d)) (hcard : S.card = m)
    (X : Ω → Fin d → ℝ) : Ω → Fin m → ℝ :=
  fun ω j => X ω ((finsetEquivFin S) (j.cast hcard.symm))

/-- Restrict a sample $X_1, \ldots, X_n$ of random vectors in $\mathbb{R}^d$ to the
coordinates indexed by `S ⊆ Fin d`, yielding a sample in $\mathbb{R}^m$. -/
def restrictSamples {Ω : Type*} {n : ℕ} (S : Finset (Fin d)) (hcard : S.card = m)
    (X : Fin n → Ω → Fin d → ℝ) : Fin n → Ω → Fin m → ℝ :=
  fun i => restrictVec S hcard (X i)

/-- The covariance of the restricted samples is the corresponding submatrix of
the original covariance matrix. -/
lemma covariance_restrict
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {m n : ℕ} (X : Fin n → Ω → Fin d → ℝ)
    (covMat : Matrix (Fin d) (Fin d) ℝ)
    (S : Finset (Fin d)) (hcard : S.card = m)
    (hcov : ∀ (i : Fin n) (j k : Fin d),
      ∫ ω, X i ω j * X i ω k ∂μ = covMat j k)
    (i : Fin n) (j k : Fin m) :
    ∫ ω, restrictSamples S hcard X i ω j * restrictSamples S hcard X i ω k ∂μ =
      covMat ((finsetEquivFin S) (j.cast hcard.symm))
            ((finsetEquivFin S) (k.cast hcard.symm)) := by
  simp only [restrictSamples, restrictVec]
  exact hcov i _ _

/-- If $\|Av\| \le M$ for every unit vector $v$, then $\|A\|_{op} \le M$. -/
lemma matOpNorm_le_of_bound {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ v : EuclideanSpace ℝ (Fin k), ‖v‖ = 1 →
      ‖(EuclideanSpace.equiv (Fin k) ℝ).symm (A.mulVec v)‖ ≤ M) :
    matOpNorm A ≤ M := by
  apply ciSup_le; intro v
  by_cases hv : ‖v‖ = 1
  · rw [ciSup_pos hv]; exact h v hv
  · rw [ciSup_neg hv, Real.sSup_empty]; exact hM

/-- The family of values $\sup_{\|v\|=1} \|Av\|$ over vectors $v$ is bounded
above (by $\sum_{i,j} |A_{ij}|$), so the supremum defining `matOpNorm` is finite. -/
lemma matOpNorm_bddAbove {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) :
    BddAbove (Set.range (fun v : EuclideanSpace ℝ (Fin k) =>
      ⨆ (_ : ‖v‖ = 1), ‖(EuclideanSpace.equiv (Fin k) ℝ).symm (A.mulVec v)‖)) := by
  use ∑ i : Fin k, ∑ j : Fin k, |A i j|
  intro x hx
  simp only [Set.mem_range] at hx
  obtain ⟨v, rfl⟩ := hx
  by_cases hv : ‖v‖ = 1
  · rw [ciSup_pos hv, EuclideanSpace.norm_eq]
    have hB : (0 : ℝ) ≤ ∑ i : Fin k, ∑ j : Fin k, |A i j| :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
    rw [Real.sqrt_le_left hB]
    have hcomp : ∀ i : Fin k, ‖(A.mulVec (v : Fin k → ℝ)) i‖ ≤ ∑ j : Fin k, |A i j| := by
      intro i
      simp only [Matrix.mulVec, dotProduct]
      calc ‖∑ j, A i j * v j‖
          ≤ ∑ j, ‖A i j * v j‖ := norm_sum_le _ _
        _ ≤ ∑ j, |A i j| := by
            apply Finset.sum_le_sum; intro j _
            rw [Real.norm_eq_abs, abs_mul]
            calc |A i j| * |v j| ≤ |A i j| * 1 := by
                  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                  calc |v j| = ‖v j‖ := (Real.norm_eq_abs _).symm
                    _ ≤ ‖v‖ := PiLp.norm_apply_le v j
                    _ = 1 := hv
              _ = |A i j| := mul_one _
    calc ∑ i, ‖(A.mulVec (v : Fin k → ℝ)) i‖ ^ 2
        ≤ ∑ i : Fin k, (∑ j : Fin k, |A i j|) ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          exact sq_le_sq' (by linarith [norm_nonneg ((A.mulVec (v : Fin k → ℝ)) i), hcomp i]) (hcomp i)
      _ ≤ (∑ i : Fin k, ∑ j : Fin k, |A i j|) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  · rw [ciSup_neg hv, Real.sSup_empty]
    exact Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => abs_nonneg _))

/-- The operator norm of a principal submatrix is bounded by the operator norm of
the original matrix: $\|A_{S,S}\|_{op} \le \|A\|_{op}$. -/
theorem matOpNorm_submatrix_le
    {m : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (S : Finset (Fin d)) (hcard : S.card = m) :
    matOpNorm (d := m) (A.submatrix
      (fun j : Fin m => ((finsetEquivFin S) (j.cast hcard.symm)).val)
      (fun j : Fin m => ((finsetEquivFin S) (j.cast hcard.symm)).val)) ≤
    matOpNorm A := by
  set f : Fin m → Fin d := fun j => ((finsetEquivFin S) (j.cast hcard.symm)).val with hf_def
  have hf_inj : Function.Injective f := by
    intro a b hab
    exact Fin.ext (Fin.val_eq_of_eq (Fin.cast_injective hcard.symm
      ((finsetEquivFin S).injective (Subtype.val_injective hab))))
  apply matOpNorm_le_of_bound _ _
    (Real.iSup_nonneg (fun v => Real.iSup_nonneg (fun _ => norm_nonneg _)))
  intro vE hvE

  let v' : Fin d → ℝ := fun j' => if h : j' ∈ S then
    (vE : Fin m → ℝ) (Fin.cast hcard ((finsetEquivFin S).symm ⟨j', h⟩)) else 0
  let v'E : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 (Fin d → ℝ)).symm v'

  have hv'_eq : ∀ j : Fin m, v' (f j) = (vE : Fin m → ℝ) j := by
    intro j; simp only [v', hf_def]
    rw [dif_pos ((finsetEquivFin S) (Fin.cast hcard.symm j)).prop]
    simp [Equiv.symm_apply_apply]

  have hv'E : ‖v'E‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have hsum : ∑ j : Fin d,
        ‖(if h : j ∈ S then (vE : Fin m → ℝ) (Fin.cast hcard ((finsetEquivFin S).symm ⟨j, h⟩)) else 0)‖ ^ 2 =
        ∑ j : Fin m, ‖(vE : Fin m → ℝ) j‖ ^ 2 := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
      have hzero : ∑ x ∈ Finset.univ.filter (fun j => j ∉ S),
          ‖(if h : x ∈ S then (vE : Fin m → ℝ) (Fin.cast hcard ((finsetEquivFin S).symm ⟨x, h⟩)) else 0)‖ ^ 2 = 0 := by
        apply Finset.sum_eq_zero; intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp [dif_neg hx]
      rw [hzero, add_zero]
      have hfilt : Finset.filter (· ∈ S) Finset.univ = S := by ext; simp
      rw [hfilt]
      symm
      apply Finset.sum_nbij
        (fun (x : Fin m) => ((finsetEquivFin S) (Fin.cast hcard.symm x) : Fin d))
      · intro a _; exact ((finsetEquivFin S) (Fin.cast hcard.symm a)).prop
      · intro a₁ _ a₂ _ h
        exact Fin.ext (Fin.val_eq_of_eq (Fin.cast_injective hcard.symm
          ((finsetEquivFin S).injective (Subtype.val_injective h))))
      · intro b hb
        simp only [Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and]
        obtain ⟨j, hj⟩ := (finsetEquivFin S).surjective ⟨b, hb⟩
        exact ⟨Fin.cast hcard j, by simp [hj]⟩
      · intro a _
        congr 1; simp only [dif_pos ((finsetEquivFin S) (Fin.cast hcard.symm a)).prop]
        congr 1; simp [Equiv.symm_apply_apply]
    change √(∑ i, ‖(if h : i ∈ S then (vE : Fin m → ℝ) (Fin.cast hcard ((finsetEquivFin S).symm ⟨i, h⟩)) else 0)‖ ^ 2) = 1
    rw [hsum, ← EuclideanSpace.norm_eq, hvE]

  have hmulvec : ∀ i : Fin m, (A.submatrix f f).mulVec (vE : Fin m → ℝ) i =
      (A.mulVec v') (f i) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
    simp only [Finset.filter_not]
    have hzero : ∑ x ∈ Finset.univ \ Finset.filter (· ∈ S) Finset.univ,
        A (f i) x * v' x = 0 := by
      apply Finset.sum_eq_zero; intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hx
      simp only [v', dif_neg hx, mul_zero]
    rw [hzero, add_zero]
    have hfilt : Finset.filter (· ∈ S) Finset.univ = S := by ext; simp
    rw [hfilt]
    apply Finset.sum_nbij
      (fun (x : Fin m) => ((finsetEquivFin S) (Fin.cast hcard.symm x) : Fin d))
    · intro a _; exact ((finsetEquivFin S) (Fin.cast hcard.symm a)).prop
    · intro a₁ _ a₂ _ h
      exact Fin.ext (Fin.val_eq_of_eq (Fin.cast_injective hcard.symm
        ((finsetEquivFin S).injective (Subtype.val_injective h))))
    · intro b hb
      simp only [Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and]
      obtain ⟨j, hj⟩ := (finsetEquivFin S).surjective ⟨b, hb⟩
      exact ⟨Fin.cast hcard j, by simp [hj]⟩
    · intro a _; congr 1; exact (hv'_eq a).symm

  have hnorm_le : ‖(EuclideanSpace.equiv (Fin m) ℝ).symm ((A.submatrix f f).mulVec vE)‖ ≤
      ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v'E)‖ := by
    simp only [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i : Fin m, ‖((A.submatrix f f).mulVec (vE : Fin m → ℝ)) i‖ ^ 2
        = ∑ i : Fin m, ‖(A.mulVec v') (f i)‖ ^ 2 := by
          congr 1; ext i; rw [hmulvec]
      _ = ∑ j ∈ Finset.univ.image f, ‖(A.mulVec v') j‖ ^ 2 := by
          rw [Finset.sum_image (fun a _ b _ h => hf_inj h)]
      _ ≤ ∑ j : Fin d, ‖(A.mulVec v') j‖ ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact fun x _ => Finset.mem_univ x
          · intro i _ _; positivity

  calc ‖(EuclideanSpace.equiv (Fin m) ℝ).symm ((A.submatrix f f).mulVec vE)‖
      ≤ ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v'E)‖ := hnorm_le
    _ ≤ ⨆ (_ : ‖v'E‖ = 1), ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v'E)‖ := by
        rw [ciSup_pos hv'E]
    _ ≤ matOpNorm A := le_ciSup (matOpNorm_bddAbove A) v'E



end Rigollet.Chapter4.Thm_4_10_Bridges
