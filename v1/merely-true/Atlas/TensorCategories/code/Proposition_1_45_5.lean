/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FrobeniusPerron

open FusionRing Matrix BigOperators

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : FusionRing ι} (fpd : R.FPdimData)

/-- Proposition 1.45.5: For a transitive unital `ℤ₊`-ring `A` of finite rank with
Frobenius–Perron data, (1) `FPdim : A → ℂ` is a ring homomorphism; (2) there is a unique
(up to scaling) regular element `R` with `XR = FPdim(X) R` for all `X`, which after
normalization has positive coefficients, satisfies `FPdim(R) > 0` and `RY = FPdim(Y) R`;
(3) `FPdim` is the unique nonzero character of `A` taking nonnegative values on the basis;
and (4) if `X` has nonnegative coefficients then `FPdim(X)` is the largest nonnegative
eigenvalue of the multiplication matrix `N_X`. -/
theorem Proposition_1_45_5 [Nonempty ι] [HasPerronFrobeniusProperty ι] :

    (fpd.d R.unit = 1 ∧
     (∀ i j, fpd.d i * fpd.d j = ∑ k : ι, (R.N i j k : ℝ) * fpd.d k)) ∧

    ((∀ X, (R.leftMulMatrixR X).mulVec fpd.d = fpd.d X • fpd.d) ∧
     (∀ i, fpd.d i > 0) ∧
     (fpd.catDim > 0) ∧
     (∀ j Y, ∑ k, (R.N j Y k : ℝ) * fpd.d k = fpd.d j * fpd.d Y) ∧
     (∀ (w : ι → ℝ) (r : ℝ), (∀ i, 0 < w i) →
       R.rightMulMatrix.mulVec w = r • w →
       ∃ c : ℝ, ∀ i, w i = c * fpd.d i)) ∧

    (∀ (χ : ι → ℝ), χ R.unit = 1 → (∀ i, 0 ≤ χ i) →
     (∀ i j, χ i * χ j = ∑ k : ι, (R.N i j k : ℝ) * χ k) →
     ∀ i, χ i = fpd.d i) ∧

    (∀ X, (R.leftMulMatrixR X).mulVec fpd.d = fpd.d X • fpd.d) :=
  ⟨fpd.proposition_1_45_5_part1,
   fpd.proposition_1_45_5_part2,
   fun χ hχ_unit hχ_nonneg hχ_mul => fpd.proposition_1_45_5_part3 χ hχ_unit hχ_nonneg hχ_mul,
   fpd.proposition_1_45_5_part4⟩

end FusionRing

/-- Top-level alias for `FusionRing.Proposition_1_45_5`. -/
abbrev proposition_1_45_5 := @FusionRing.Proposition_1_45_5
