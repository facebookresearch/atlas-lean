/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.Module.SpanRankOperations

set_option maxHeartbeats 400000

open IsLocalRing

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Lemma 30 (Lecture 18): For a Noetherian local ring `R`, the Krull dimension is bounded above
by the residue-field dimension of the Zariski cotangent space, i.e. `dim R ≤ dim T*_x X`. -/
theorem cotangentSpace_dim_ge_krullDim :
    ringKrullDim R ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by
  rw [← maximalIdeal_height_eq_ringKrullDim]
  have h := Ideal.height_le_spanFinrank (maximalIdeal R) (Ideal.IsPrime.ne_top')
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R] at h
  exact_mod_cast h
