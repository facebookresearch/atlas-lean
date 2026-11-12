/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec5DimensionResults

set_option maxHeartbeats 400000

/-- Theorem 5.1: The affine `n`-space `A^n = Spec k[x₁,…,xₙ]` has Krull dimension `n`. -/
theorem dim_affine_space_eq (k : Type*) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = ↑n := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    zero_add, Nat.card_fin]

/-- Every finitely generated `k`-algebra has finite Krull dimension (i.e. not `⊤`). -/
theorem variety_finite_krullDim (k : Type*) [Field k]
    (A : Type*) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A ≠ ⊤ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  have h := ringKrullDim_le_of_surjective (f : MvPolynomial (Fin n) k →+* A) hf
  rw [dim_affine_space_eq] at h
  intro htop
  rw [htop] at h
  exact absurd h (by nofun)
