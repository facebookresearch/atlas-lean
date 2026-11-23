/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.CkBanach
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

open scoped ZeroAtInfty
open Filter Topology Finset

noncomputable section

set_option maxRecDepth 4000

namespace TestFunctions

variable {n : ℕ}

/-- The range of the pointwise norm of a `ContDiffZeroAtInfty` element is bounded above. -/
lemma ContDiffZeroAtInfty.bddAbove_range_norm_val (u : ContDiffZeroAtInfty n) :
    BddAbove (Set.range (fun x => ‖u.toZeroAtInftyContinuousMap x‖)) :=
  ⟨‖u.toZeroAtInftyContinuousMap.toBCF‖, by
    rintro _ ⟨x, rfl⟩; exact u.toZeroAtInftyContinuousMap.toBCF.norm_coe_le_norm x⟩

/-- The `j`-th partial derivative of a `ContDiffZeroAtInfty` element is continuous. -/
lemma ContDiffZeroAtInfty.continuous_partialDeriv (u : ContDiffZeroAtInfty n) (j : Fin n) :
    Continuous (fun x => fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x
      (EuclideanSpace.single j 1)) := by
  have hcont_fderiv : Continuous (fderiv ℝ (⇑u.toZeroAtInftyContinuousMap)) :=
    u.contDiff_one.continuous_fderiv (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single j 1)).continuous.comp hcont_fderiv

/-- The `j`-th partial derivative of `u` as a `C₀` continuous function (vanishing at infinity). -/
def ContDiffZeroAtInfty.partialDerivC0 (u : ContDiffZeroAtInfty n) (j : Fin n) :
    C₀(EuclideanSpace ℝ (Fin n), ℂ) where
  toFun x := fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)
  continuous_toFun := u.continuous_partialDeriv j
  zero_at_infty' := u.partialDeriv_zero_at_infty j

/-- The range of the norm of the `j`-th partial derivative is bounded above. -/
lemma ContDiffZeroAtInfty.bddAbove_range_norm_deriv (u : ContDiffZeroAtInfty n) (j : Fin n) :
    BddAbove (Set.range (fun x => ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x
      (EuclideanSpace.single j 1)‖)) :=
  ⟨‖(u.partialDerivC0 j).toBCF‖, by
    rintro _ ⟨x, rfl⟩; exact (u.partialDerivC0 j).toBCF.norm_coe_le_norm x⟩

/-- Pointwise norm of `u` at `x` is bounded by the supremum of `‖u y‖`. -/
lemma ContDiffZeroAtInfty.norm_apply_le_iSup (u : ContDiffZeroAtInfty n) (x) :
    ‖u.toZeroAtInftyContinuousMap x‖ ≤ ⨆ y, ‖u.toZeroAtInftyContinuousMap y‖ :=
  le_ciSup u.bddAbove_range_norm_val x

/-- Pointwise norm of the `j`-th partial derivative at `x` is bounded by the supremum. -/
lemma ContDiffZeroAtInfty.norm_deriv_apply_le_iSup (u : ContDiffZeroAtInfty n)
    (j : Fin n) (x) :
    ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖ ≤
    ⨆ y, ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) y (EuclideanSpace.single j 1)‖ :=
  le_ciSup (u.bddAbove_range_norm_deriv j) x

/-- Triangle inequality for the `C^1₀` norm on `ContDiffZeroAtInfty n`. -/
lemma ContDiffZeroAtInfty.c1_norm_add_le (u v : ContDiffZeroAtInfty n) :
    ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
  show ckNorm n 1 _ ≤ ckNorm n 1 _ + ckNorm n 1 _
  simp only [ckNorm]
  have hudiff := u.differentiable
  have hvdiff := v.differentiable
  have hcoe_add : ∀ x, (u + v).toZeroAtInftyContinuousMap x =
      u.toZeroAtInftyContinuousMap x + v.toZeroAtInftyContinuousMap x := fun _ => rfl
  have hcoe_add_fn : (⇑(u + v).toZeroAtInftyContinuousMap : _ → ℂ) =
      ⇑u.toZeroAtInftyContinuousMap + ⇑v.toZeroAtInftyContinuousMap :=
    funext hcoe_add
  have hfderiv_add : ∀ j x,
      fderiv ℝ (⇑(u + v).toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1) =
      fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1) +
      fderiv ℝ (⇑v.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1) := by
    intro j x
    rw [hcoe_add_fn, fderiv_add (hudiff x) (hvdiff x), ContinuousLinearMap.add_apply]
  have h1 : (⨆ x, ‖(u + v).toZeroAtInftyContinuousMap x‖) ≤
      (⨆ x, ‖u.toZeroAtInftyContinuousMap x‖) +
      (⨆ x, ‖v.toZeroAtInftyContinuousMap x‖) :=
    ciSup_le fun x => (hcoe_add x ▸ norm_add_le _ _).trans
      (add_le_add (u.norm_apply_le_iSup x) (v.norm_apply_le_iSup x))
  have h2 : ∀ j : Fin n,
      (⨆ x, ‖fderiv ℝ (⇑(u + v).toZeroAtInftyContinuousMap) x
        (EuclideanSpace.single j 1)‖) ≤
      (⨆ x, ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖) +
      (⨆ x, ‖fderiv ℝ (⇑v.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖) :=
    fun j => ciSup_le fun x => (hfderiv_add j x ▸ norm_add_le _ _).trans
      (add_le_add (u.norm_deriv_apply_le_iSup j x) (v.norm_deriv_apply_le_iSup j x))
  have h3 : (∑ j : Fin n, ⨆ x,
      ‖fderiv ℝ (⇑(u + v).toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖) ≤
      (∑ j : Fin n, ⨆ x,
        ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖) +
      (∑ j : Fin n, ⨆ x,
        ‖fderiv ℝ (⇑v.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => h2 j
  linarith

/-- Scalar homogeneity of the `C^1₀` norm: `‖c • u‖ = ‖c‖ * ‖u‖`. -/
lemma ContDiffZeroAtInfty.c1_norm_smul (c : ℂ) (u : ContDiffZeroAtInfty n) :
    ‖c • u‖ = ‖c‖ * ‖u‖ := by
  show ckNorm n 1 _ = ‖c‖ * ckNorm n 1 _
  simp only [ckNorm]
  have hudiff := u.differentiable
  have hcoe_smul_fn : (⇑(c • u).toZeroAtInftyContinuousMap : _ → ℂ) =
      c • ⇑u.toZeroAtInftyContinuousMap := funext (fun _ => rfl)
  have hcoe_smul : ∀ x, (c • u).toZeroAtInftyContinuousMap x =
      c • u.toZeroAtInftyContinuousMap x := fun _ => rfl
  have hfderiv_smul : ∀ j x,
      fderiv ℝ (⇑(c • u).toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1) =
      c • fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1) := by
    intro j x
    rw [hcoe_smul_fn, fderiv_const_smul (hudiff x) c, ContinuousLinearMap.smul_apply]
  have h_val : (⨆ x, ‖(c • u).toZeroAtInftyContinuousMap x‖) =
      ‖c‖ * (⨆ x, ‖u.toZeroAtInftyContinuousMap x‖) := by
    have : (fun x => ‖(c • u).toZeroAtInftyContinuousMap x‖) =
        (fun x => ‖c‖ * ‖u.toZeroAtInftyContinuousMap x‖) :=
      funext fun x => by rw [hcoe_smul, norm_smul]
    rw [this, ← Real.mul_iSup_of_nonneg (norm_nonneg c)]
  have h_deriv : ∀ j : Fin n,
      (⨆ x, ‖fderiv ℝ (⇑(c • u).toZeroAtInftyContinuousMap) x
        (EuclideanSpace.single j 1)‖) =
      ‖c‖ * (⨆ x, ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x
        (EuclideanSpace.single j 1)‖) := by
    intro j
    have : (fun x => ‖fderiv ℝ (⇑(c • u).toZeroAtInftyContinuousMap) x
        (EuclideanSpace.single j 1)‖) =
        (fun x => ‖c‖ * ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x
          (EuclideanSpace.single j 1)‖) :=
      funext fun x => by rw [hfderiv_smul, norm_smul]
    rw [this, ← Real.mul_iSup_of_nonneg (norm_nonneg c)]
  rw [h_val]
  simp_rw [h_deriv]
  rw [← Finset.mul_sum, ← mul_add]

/-- Separation: the `C^1₀` norm vanishes iff the element is zero. -/
lemma ContDiffZeroAtInfty.c1_norm_eq_zero_iff (u : ContDiffZeroAtInfty n) :
    ‖u‖ = 0 ↔ u = 0 := by
  constructor
  · intro h
    have h' : ckNorm n 1 ⇑u.toZeroAtInftyContinuousMap = 0 := h
    simp only [ckNorm] at h'
    have h_nn_val := Real.iSup_nonneg fun x => norm_nonneg (u.toZeroAtInftyContinuousMap x)
    have h_nn_sum : 0 ≤ ∑ j : Fin n, ⨆ x,
        ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖ :=
      Finset.sum_nonneg fun j _ =>
        Real.iSup_nonneg fun x => norm_nonneg
          (fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1))
    have h_val_zero : ⨆ x, ‖u.toZeroAtInftyContinuousMap x‖ = 0 := by linarith
    have hpw : ∀ x, u.toZeroAtInftyContinuousMap x = 0 := by
      intro x
      have hle := u.norm_apply_le_iSup x
      rw [h_val_zero] at hle
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    exact ContDiffZeroAtInfty.toC0_injective (DFunLike.ext _ _ hpw)
  · intro h; rw [h]; exact ContDiffZeroAtInfty.c1_norm_zero

/-- Core data for the `NormedSpace` structure on `ContDiffZeroAtInfty n`. -/
lemma ContDiffZeroAtInfty.normedSpaceCore :
    NormedSpace.Core ℂ (ContDiffZeroAtInfty n) where
  norm_nonneg := ContDiffZeroAtInfty.c1_norm_nonneg
  norm_smul := ContDiffZeroAtInfty.c1_norm_smul
  norm_triangle := ContDiffZeroAtInfty.c1_norm_add_le
  norm_eq_zero_iff := ContDiffZeroAtInfty.c1_norm_eq_zero_iff

/-- The `NormedAddCommGroup` instance on `ContDiffZeroAtInfty n` via the `C^1₀` norm. -/
instance ContDiffZeroAtInfty.instNormedAddCommGroup :
    NormedAddCommGroup (ContDiffZeroAtInfty n) :=
  NormedAddCommGroup.ofCore ContDiffZeroAtInfty.normedSpaceCore

/-- The `ℂ`-`NormedSpace` instance on `ContDiffZeroAtInfty n`. -/
instance ContDiffZeroAtInfty.instNormedSpace :
    NormedSpace ℂ (ContDiffZeroAtInfty n) :=
  NormedSpace.ofCore ContDiffZeroAtInfty.normedSpaceCore

/-- The `j`-th partial derivative is additive on differences. -/
lemma ContDiffZeroAtInfty.sub_partialDerivC0 (u v : ContDiffZeroAtInfty n) (j : Fin n) :
    (u - v).partialDerivC0 j = u.partialDerivC0 j - v.partialDerivC0 j := by
  ext x
  simp only [partialDerivC0, ZeroAtInftyContinuousMap.coe_mk,
    ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply]

  have hu := u.differentiable x
  have hv := v.differentiable x
  have : (⇑(u - v).toZeroAtInftyContinuousMap : _ → ℂ) =
      ⇑u.toZeroAtInftyContinuousMap - ⇑v.toZeroAtInftyContinuousMap := funext (fun _ => rfl)
  rw [this, fderiv_sub hu hv, ContinuousLinearMap.sub_apply]

/-- The `C₀` norm of the underlying continuous map is bounded by the `C^1₀` norm. -/
lemma ContDiffZeroAtInfty.c0_norm_le (f : ContDiffZeroAtInfty n) :
    ‖f.toZeroAtInftyContinuousMap‖ ≤ ‖f‖ := by
  rw [f.norm_def]
  have : ‖f.toZeroAtInftyContinuousMap‖ =
      ⨆ x, ‖f.toZeroAtInftyContinuousMap x‖ := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
        BoundedContinuousFunction.norm_eq_iSup_norm]
    rfl
  rw [this]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ =>
    Real.iSup_nonneg fun x => norm_nonneg _)

/-- The `C₀` norm of the `j`-th partial derivative is bounded by the `C^1₀` norm of `f`. -/
lemma ContDiffZeroAtInfty.pd_norm_le (f : ContDiffZeroAtInfty n) (j : Fin n) :
    ‖f.partialDerivC0 j‖ ≤ ‖f‖ := by
  rw [f.norm_def]
  have hpd_norm : ‖f.partialDerivC0 j‖ =
      ⨆ x, ‖(f.partialDerivC0 j) x‖ := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
        BoundedContinuousFunction.norm_eq_iSup_norm]
    rfl
  rw [hpd_norm]
  have h_nn : 0 ≤ ⨆ x, ‖f.toZeroAtInftyContinuousMap x‖ :=
    Real.iSup_nonneg fun x => norm_nonneg _
  calc ⨆ x, ‖(f.partialDerivC0 j) x‖
      ≤ ∑ i : Fin n, ⨆ x, ‖(f.partialDerivC0 i) x‖ :=
        Finset.single_le_sum (f := fun i => ⨆ x, ‖(f.partialDerivC0 i) x‖)
          (fun i _ => Real.iSup_nonneg fun x => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ (⨆ x, ‖f.toZeroAtInftyContinuousMap x‖) +
        ∑ i : Fin n, ⨆ x, ‖(f.partialDerivC0 i) x‖ :=
        le_add_of_nonneg_left h_nn
    _ = (⨆ x, ‖f.toZeroAtInftyContinuousMap x‖) +
        ∑ i : Fin n, ⨆ x,
          ‖fderiv ℝ (⇑f.toZeroAtInftyContinuousMap) x (EuclideanSpace.single i 1)‖ := by
        congr 1

end TestFunctions

end

open scoped ZeroAtInfty
open Filter Topology Finset




noncomputable section

open scoped ZeroAtInfty
open Filter Topology Finset TestFunctions

set_option maxRecDepth 8000
set_option maxHeartbeats 800000


end
