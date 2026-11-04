/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AnAlgorithmistsToolkit.code.BrunnMinkowski
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace BrunnMinkowskiInequality

open MeasureTheory Measure Pointwise






end BrunnMinkowskiInequality

namespace BrunnsTheorem

open MeasureTheory Set Pointwise
open scoped ENNReal NNReal

def parallelSlice {n : ℕ} (K : Set (Fin (n + 1) → ℝ)) (t : ℝ) : Set (Fin n → ℝ) :=
  {y : Fin n → ℝ | Fin.cons t y ∈ K}

noncomputable def sliceVolume {n : ℕ} (K : Set (Fin (n + 1) → ℝ)) (t : ℝ) : ℝ≥0∞ :=
  volume (parallelSlice K t)

noncomputable def brunnFunction (n : ℕ) (K : Set (Fin (n + 1) → ℝ)) (t : ℝ) : ℝ :=
  (sliceVolume K t).toReal ^ ((1 : ℝ) / (n : ℝ))

variable {n : ℕ}



lemma slice_minkowski_subset (K : Set (Fin (n + 1) → ℝ)) (hK : Convex ℝ K)
    (r t : ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • (parallelSlice K r) + b • (parallelSlice K t) ⊆ parallelSlice K (a * r + b * t) := by
  intro z hz
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_add.mp hz
  obtain ⟨x, hx, hux⟩ := Set.mem_smul_set.mp hu
  obtain ⟨y, hy, hvy⟩ := Set.mem_smul_set.mp hv
  show Fin.cons (a * r + b * t) z ∈ K
  have key : a • (Fin.cons r x : Fin (n+1) → ℝ) + b • (Fin.cons t y : Fin (n+1) → ℝ) =
      (Fin.cons (a * r + b * t) (a • x + b • y) : Fin (n+1) → ℝ) := by
    funext i; refine Fin.cases ?_ ?_ i
    · simp [Pi.smul_apply, Pi.add_apply, Fin.cons_zero, smul_eq_mul]
    · intro j; simp [Pi.smul_apply, Pi.add_apply, Fin.cons_succ, smul_eq_mul]
  have hzeq : z = a • x + b • y := by
    rw [← hux, ← hvy] at huv; exact huv.symm
  rw [hzeq, ← key]; exact hK hx hy ha hb hab



end BrunnsTheorem
