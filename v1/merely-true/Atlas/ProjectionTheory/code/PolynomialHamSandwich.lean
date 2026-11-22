/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.BorsukUlam

open MeasureTheory MvPolynomial

noncomputable section

namespace PolynomialHamSandwich

/-- A polynomial `P : ℝ[x₁, …, x_d]` *bisects* a measurable set `U ⊆ ℝ^d` if the
parts of `U` where `P > 0` and where `P < 0` have equal Lebesgue volume. -/
def Bisects (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (U : Set (Fin d → ℝ)) : Prop :=
  volume ({x ∈ U | eval x P > 0}) =
    volume ({x ∈ U | eval x P < 0})

/-- The signed volume `vol{P > 0 in U} − vol{P < 0 in U}` as a real number; this
function is zero exactly when `P` bisects `U` (assuming `U` is bounded). -/
def signedVol (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (U : Set (Fin d → ℝ)) : ℝ :=
  (volume ({x ∈ U | eval x P > 0})).toReal -
    (volume ({x ∈ U | eval x P < 0})).toReal

/-- Negating the polynomial flips the sign of the signed volume:
`signedVol(−P, U) = −signedVol(P, U)`. -/
lemma signedVol_neg (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (U : Set (Fin d → ℝ)) :
    signedVol d (-P) U = -(signedVol d P U) := by
  simp only [signedVol, eval_neg, neg_pos, neg_lt_zero, neg_sub]

/-- For a bounded set `U`, vanishing of the signed volume `signedVol d P U` implies
that `P` bisects `U`. -/
lemma bisects_of_signedVol_zero (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (U : Set (Fin d → ℝ))
    (hU_bounded : Bornology.IsBounded U) (h : signedVol d P U = 0) : Bisects d P U := by
  unfold Bisects signedVol at *
  have hfp : volume ({x ∈ U | eval x P > 0}) ≠ ⊤ :=
    (Bornology.IsBounded.measure_lt_top (μ := volume)
      (hU_bounded.subset (Set.sep_subset U _))).ne
  have hfn : volume ({x ∈ U | eval x P < 0}) ≠ ⊤ :=
    (Bornology.IsBounded.measure_lt_top (μ := volume)
      (hU_bounded.subset (Set.sep_subset U _))).ne
  exact (ENNReal.toReal_eq_toReal_iff' hfp hfn).mp (by linarith)

/-- A nontrivial linear combination of linearly independent polynomials is nonzero. -/
lemma combo_ne_zero {d m : ℕ} (basis : Fin m → MvPolynomial (Fin d) ℝ)
    (hbasis : LinearIndependent ℝ basis) (v : Fin m → ℝ) (hv : v ≠ 0) :
    ∑ i, v i • basis i ≠ 0 := by
  intro h; rw [linearIndependent_iff'] at hbasis
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hall; push Not at hall; exact hv (funext hall)
  exact hj (hbasis Finset.univ v h j (Finset.mem_univ j))

/-- Any real-linear combination of polynomials of total degree at most `D` itself
has total degree at most `D`. -/
lemma combo_totalDegree_le {d D m : ℕ} (basis : Fin m → MvPolynomial (Fin d) ℝ)
    (hbasis_deg : ∀ i, (basis i).totalDegree ≤ D) (v : Fin m → ℝ) :
    (∑ i, v i • basis i).totalDegree ≤ D :=
  le_trans (totalDegree_finset_sum _ _)
    (Finset.sup_le (fun i _ => le_trans (totalDegree_smul_le _ _) (hbasis_deg i)))

/-- A point on the unit sphere `S^n ⊆ ℝ^{n+1}` has, in particular, a nonzero
coordinate vector. -/
lemma sphere_vec_ne_zero {n : ℕ} (x : ↥(BorsukUlam.Sphere n)) :
    (fun i => (x : EuclideanSpace ℝ (Fin (n + 1))) i) ≠ 0 := by
  intro h
  have hx := x.property
  simp only [BorsukUlam.Sphere, Metric.mem_sphere, dist_zero_right] at hx
  have : (x : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by ext i; exact congr_fun h i
  rw [this, norm_zero] at hx; exact one_ne_zero hx.symm







end PolynomialHamSandwich
