/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec5DimensionResults

set_option maxHeartbeats 400000

noncomputable section

/-- Lecture 5, Theorem 5.1: affine `n`-space has dimension `n`, i.e. `dim k[x_1, …, x_n] = n`. -/
theorem thm51_dim_affine_space (k : Type*) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp

/-- Lecture 5, Corollary 11: any algebraic variety over a field is finite-dimensional, since any
finitely generated `k`-algebra has finite Krull dimension. -/
theorem cor11_variety_finite_dim (k : Type*) [Field k]
    (A : Type*) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A < ⊤ := by

  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›

  have h1 : ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin n) k) :=
    ringKrullDim_le_of_surjective f.toRingHom hf

  have h2 : ringKrullDim (MvPolynomial (Fin n) k) < ⊤ := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_isField (Field.toIsField k)]
    simp only [zero_add]
    exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)
  exact lt_of_le_of_lt h1 h2

end
