/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

open Polynomial IntermediateField Module

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The `natDegree` of the minimal polynomial of any element of a finite extension
is bounded by the degree of the extension. -/
theorem minpoly_natDegree_le_finrank (α : L) [FiniteDimensional K L] :
    (minpoly K α).natDegree ≤ finrank K L :=
  minpoly.natDegree_le α

/-- The polynomial degree of the minimal polynomial of any element of a finite
extension is bounded by the degree of the extension. -/
theorem minpoly_degree_le_finrank (α : L) [FiniteDimensional K L] :
    (minpoly K α).degree ≤ ↑(finrank K L) :=
  minpoly.degree_le α

/-- The degree of the minimal polynomial of any element of a finite extension
divides the degree of the extension. -/
theorem minpoly_natDegree_dvd_finrank (α : L) [FiniteDimensional K L] :
    (minpoly K α).natDegree ∣ finrank K L :=
  minpoly.degree_dvd (IsIntegral.of_finite K α)
