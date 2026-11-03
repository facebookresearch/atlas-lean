/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FiniteTensorCategory

open Finset CategoryTheory

namespace CategoryTheory.FiniteTensorCategoryData

variable (D : FiniteTensorCategoryData)

/-- Extract the absorption identity at the Grothendieck-ring level from a
left-`Hom`-level absorption hypothesis by specialising `homDim` to a Kronecker
delta. -/
theorem absorption_identity_K0_level
    (fpDimZ : ℝ)
    (tensorDecomp : D.ι → D.ι → ℝ)
    (h_hom_level : ∀ (homDim : D.ι → D.ι → ℝ),
      ∀ j : D.ι,
        (∑ i : D.ι, D.fpDimSimple i *
          (∑ k : D.ι, tensorDecomp i k * homDim k j)) =
          fpDimZ * (∑ i : D.ι, D.fpDimSimple i * homDim i j)) :
    ∀ j : D.ι,
      (∑ i : D.ι, D.fpDimSimple i * tensorDecomp i j) =
        fpDimZ * D.fpDimSimple j := by
  intro j
  have h := h_hom_level (fun k j' => if k = j' then 1 else 0) j
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h
  exact h

/-- The right-handed analogue of `absorption_identity_K0_level`: extract the
absorption identity at the Grothendieck-ring level from a right-`Hom`-level
absorption hypothesis. -/
theorem absorption_identity_K0_level_right
    (fpDimZ : ℝ)
    (tensorDecompRight : D.ι → D.ι → ℝ)
    (h_hom_level_right : ∀ (homDim : D.ι → D.ι → ℝ),
      ∀ j : D.ι,
        (∑ i : D.ι, D.fpDimSimple i *
          (∑ k : D.ι, tensorDecompRight i k * homDim k j)) =
          fpDimZ * (∑ i : D.ι, D.fpDimSimple i * homDim i j)) :
    ∀ j : D.ι,
      (∑ i : D.ι, D.fpDimSimple i * tensorDecompRight i j) =
        fpDimZ * D.fpDimSimple j := by
  intro j
  have h := h_hom_level_right (fun k j' => if k = j' then 1 else 0) j
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h
  exact h



end CategoryTheory.FiniteTensorCategoryData
