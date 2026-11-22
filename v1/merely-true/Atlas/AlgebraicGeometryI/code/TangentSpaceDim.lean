/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.Module.SpanRankOperations

set_option maxHeartbeats 400000

noncomputable section

open IsLocalRing Module

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Tangent space dimension bound (Lem 30): for a Noetherian local ring, the
Krull dimension is at most the dimension of the cotangent space `m/m²` over
the residue field, i.e. `dim T*_x X ≥ dim_x X`. -/
theorem tangentDim_ge_krullDim :
    ringKrullDim R ≤ ↑(finrank (ResidueField R) (CotangentSpace R)) := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact ringKrullDim_le_spanFinrank_maximalIdeal R

/-- A Noetherian local ring is regular (smooth) iff the dimension of its
cotangent space equals its Krull dimension. -/
theorem smooth_iff_tangentDim_eq_krullDim :
    IsRegularLocalRing R ↔
      ↑(finrank (ResidueField R) (CotangentSpace R)) = ringKrullDim R :=
  IsRegularLocalRing.iff_finrank_cotangentSpace R

/-- At a non-smooth (non-regular) point, the cotangent space dimension is
strictly greater than the Krull dimension. -/
theorem tangentDim_gt_krullDim_of_not_smooth (h : ¬IsRegularLocalRing R) :
    ringKrullDim R < ↑(finrank (ResidueField R) (CotangentSpace R)) := by
  rw [lt_iff_le_and_ne]
  exact ⟨tangentDim_ge_krullDim R,
    fun heq => h ((smooth_iff_tangentDim_eq_krullDim R).mpr heq.symm)⟩

/-- Combined statement: the cotangent dimension always upper-bounds the Krull
dimension, with equality characterizing smoothness. -/
theorem tangentSpace_dim_characterizes_smoothness :
    ringKrullDim R ≤ ↑(finrank (ResidueField R) (CotangentSpace R)) ∧
    (IsRegularLocalRing R ↔
      ↑(finrank (ResidueField R) (CotangentSpace R)) = ringKrullDim R) :=
  ⟨tangentDim_ge_krullDim R, smooth_iff_tangentDim_eq_krullDim R⟩

end
