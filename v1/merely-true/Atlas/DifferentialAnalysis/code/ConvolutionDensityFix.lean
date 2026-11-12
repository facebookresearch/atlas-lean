/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open TestFunctions
open scoped ZeroAtInfty
open Filter Topology Metric

noncomputable section

namespace ConvolutionDensity

/-- The predicate `allPdBound k f δ` asserts that all partial derivatives of
`f` of order `≤ k` (taken with respect to standard basis directions) are
bounded by `δ` in norm.  Defined recursively in `k`. -/
def allPdBound {n : ℕ} : ℕ → (EuclideanSpace ℝ (Fin n) → ℂ) → ℝ → Prop
  | 0, f, δ => ∀ x, ‖f x‖ ≤ δ
  | k + 1, f, δ => allPdBound k f δ ∧
      ∀ j : Fin n, allPdBound k (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) δ

/-- If all partial derivatives of `f` of order `≤ k` are bounded by `δ`, then
the `Cᵏ` norm is bounded by `(n+1)^k · δ`. -/
lemma ckNorm_le_of_allPdBound {n : ℕ} :
    ∀ (k : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (δ : ℝ),
    0 ≤ δ → allPdBound k f δ → ckNorm n k f ≤ ((n : ℝ) + 1) ^ k * δ := by
  intro k; induction k with
  | zero =>
    intro f δ _ hb
    simp only [ckNorm, allPdBound, pow_zero, one_mul] at *
    exact ciSup_le hb
  | succ k ih =>
    intro f δ hδ ⟨hb_f, hb_deriv⟩
    simp only [ckNorm]
    calc ckNorm n k f +
          ∑ j : Fin n, ckNorm n k (fun x => fderiv ℝ f x (EuclideanSpace.single j 1))
        ≤ ((n : ℝ) + 1) ^ k * δ + ∑ _j : Fin n, ((n : ℝ) + 1) ^ k * δ := by
          gcongr with j _
          · exact ih f δ hδ hb_f
          · exact ih _ δ hδ (hb_deriv j)
      _ = ((n : ℝ) + 1) ^ k * δ + (n : ℝ) * (((n : ℝ) + 1) ^ k * δ) := by
          congr 1; rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      _ = ((n : ℝ) + 1) ^ (k + 1) * δ := by ring

/-- Pointwise bounds on the iterated Fréchet derivatives of `f` up to order
`k` imply the recursive bound `allPdBound k f δ` on the (axis-aligned)
partial derivatives. -/
lemma allPdBound_of_iteratedFDeriv_le {n : ℕ} :
    ∀ (k : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (δ : ℝ),
    ContDiff ℝ k f →
    (∀ (m : ℕ), m ≤ k → ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ δ) →
    allPdBound k f δ := by
  intro k
  induction k with
  | zero =>
    intro f δ _ hbd x
    have := hbd 0 le_rfl x
    rwa [norm_iteratedFDeriv_zero] at this
  | succ k ih =>
    intro f δ hf hbd
    have hfk : ContDiff ℝ k f := hf.of_le (by norm_cast; omega)
    have hf_fderiv : ContDiff ℝ k (fderiv ℝ f) :=
      (contDiff_succ_iff_fderiv.mp (by exact_mod_cast hf)).2.2
    refine ⟨ih f δ hfk (fun m hm x => hbd m (le_trans hm (Nat.le_succ k)) x), ?_⟩
    intro j
    apply ih _ δ (((ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single j 1)).contDiff).comp hf_fderiv)
    intro m hm x
    have hm1 : m + 1 ≤ k + 1 := Nat.succ_le_succ hm
    have hcomp := ContinuousLinearMap.iteratedFDeriv_comp_left (x := x)
      (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single j 1))
      (hf_fderiv.contDiffAt) (i := m) (by norm_cast)
    rw [hcomp]
    calc ‖(ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single j 1)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ m (fderiv ℝ f) x)‖
        ≤ ‖ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single (j : Fin n) (1 : ℝ))‖ *
          ‖iteratedFDeriv ℝ m (fderiv ℝ f) x‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ 1 * ‖iteratedFDeriv ℝ m (fderiv ℝ f) x‖ := by
          gcongr
          apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
          intro g; simp only [ContinuousLinearMap.apply_apply]
          calc ‖g (EuclideanSpace.single j 1)‖
              ≤ ‖g‖ * ‖EuclideanSpace.single (j : Fin n) (1 : ℝ)‖ :=
                ContinuousLinearMap.le_opNorm g _
            _ = ‖g‖ * 1 := by rw [PiLp.norm_single, norm_one]
            _ = 1 * ‖g‖ := by ring
      _ = ‖iteratedFDeriv ℝ (m + 1) f x‖ := by
          rw [one_mul, norm_iteratedFDeriv_fderiv]
      _ ≤ δ := hbd (m + 1) hm1 x





end ConvolutionDensity

end
