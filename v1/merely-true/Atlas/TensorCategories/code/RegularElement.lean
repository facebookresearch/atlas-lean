/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FrobeniusPerron

open Finset

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- A family of real coefficients `coeffs` is a regular element of a fusion ring
`A` with Frobenius–Perron dimension data `fpd` if it is a simultaneous eigenvector
of left multiplication by every basis object `X` with eigenvalue `fpd.d X`. -/
def IsRegularElement (A : FusionRing ι) (fpd : A.FPdimData) (coeffs : ι → ℝ) : Prop :=
  ∀ (X k : ι), ∑ j : ι, (A.N X j k : ℝ) * coeffs j = fpd.d X * coeffs k

/-- A regular element of a fusion ring `R`: a positive vector `r` that is absorbed
on both sides by multiplication with eigenvalue equal to the Frobenius–Perron
dimension, and whose Frobenius–Perron norm `∑ d_i · r_i` is positive. -/
structure RegularElement (R : FusionRing ι) (fpd : R.FPdimData) where
  r : ι → ℝ
  r_pos : ∀ i, 0 < r i
  left_absorb : ∀ (X k : ι),
    ∑ j : ι, (R.N X j k : ℝ) * r j = fpd.d X * r k
  right_absorb : ∀ (Y k : ι),
    ∑ j : ι, (R.N j Y k : ℝ) * r j = fpd.d Y * r k
  fpdim_pos : 0 < ∑ i : ι, fpd.d i * r i

/-- The underlying coefficient vector of a `RegularElement` is a regular element
in the sense of `IsRegularElement`. -/
theorem RegularElement.isRegularElement {R : FusionRing ι} {fpd : R.FPdimData}
    (reg : R.RegularElement fpd) : R.IsRegularElement fpd reg.r :=
  reg.left_absorb

/-- The coefficients of a `RegularElement` are strictly positive. -/
theorem IsRegularElement.coeffs_pos_of_regularElement {R : FusionRing ι} {fpd : R.FPdimData}
    (reg : R.RegularElement fpd) : ∀ i, 0 < reg.r i :=
  reg.r_pos

/-- Proposition 1.45.8 (Etingof–Gelaki–Nikshych–Ostrik): The Frobenius–Perron
dimension is invariant under any anti-automorphism `star` of the fusion ring;
in particular, dimensions of dual objects equal those of the originals. -/
theorem proposition_1_45_8 {A : FusionRing ι} (fpd : A.FPdimData)
    (star : ι → ι) (hstar : A.IsAntiAutomorphism star) (X : ι) :
    fpd.d (star X) = fpd.d X :=
  fpd.fpdim_antiAut_invariant star hstar X

end FusionRing
