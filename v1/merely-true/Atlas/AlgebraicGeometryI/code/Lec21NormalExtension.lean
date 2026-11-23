/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Atlas.AlgebraicGeometryI.code.NormalExtension

open AlgebraicHartogs in
/-- An ideal of height at least `2` cannot be contained in a height-one prime. -/
theorem not_le_heightOnePrime_of_height_ge_two {A : Type*} [CommRing A]
    (I : Ideal A) (hI : 2 ≤ I.height) (p : HeightOnePrime A) : ¬(I ≤ p.asIdeal) := by
  intro hle
  have h1 : I.height ≤ p.asIdeal.height := Ideal.height_mono hle
  rw [p.height_eq] at h1
  exact absurd (le_trans hI h1) (by norm_num)

namespace Proposition39

section NormalDomain

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]


/-- The `A`-linear map `A → K` sending `a ↦ a / b`, used to realise `A[x] ⊆ K` as a
submodule of a finitely generated `A`-module when `b` clears all denominators of `A[x]`. -/
noncomputable def divByMap (b : A) : A →ₗ[A] K where
  toFun a := algebraMap A K a * (algebraMap A K b)⁻¹
  map_add' a₁ a₂ := by simp [add_mul]
  map_smul' r a := by
    simp only [RingHom.id_apply, smul_eq_mul, map_mul, Algebra.smul_def]; ring






end NormalDomain

end Proposition39
