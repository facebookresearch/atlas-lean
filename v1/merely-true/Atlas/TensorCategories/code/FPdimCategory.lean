/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FiniteTensorCategory

set_option maxHeartbeats 800000

open CategoryTheory Finset

universe u v

namespace CategoryTheory

/-- Data needed to compute the Frobenius-Perron dimension of a multitensor category `C`:
a finite nonempty index set `I`, a family of simple objects `simpleObj : I → C`, an
FP-dimension function on `C`, and the assumption that each simple has FP-dimension at
least one. -/
structure FPdimCategoryData (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  I : Type*
  [instFintype : Fintype I]
  [instNonempty : Nonempty I]
  simpleObj : I → C
  fpDimFun : FPdimFunction (C := C)
  fpDim_simpleObj_ge_one : ∀ i, fpDimFun.fpDim (simpleObj i) ≥ 1

attribute [instance] FPdimCategoryData.instFintype FPdimCategoryData.instNonempty

namespace FPdimCategoryData

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (D : FPdimCategoryData C)

/-- The Frobenius-Perron dimension of `C`, computed from the given data as the sum of
squared FP-dimensions of the chosen simple objects (EGNO Definition 6.1.6). -/
noncomputable def fpDimCategory : ℝ :=
  ∑ i : D.I, D.fpDimFun.fpDim (D.simpleObj i) ^ 2

end FPdimCategoryData

/-- Top-level alias for the Frobenius-Perron dimension of a category, packaged from its
`FPdimCategoryData`. -/
noncomputable def fpDimCategory {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (D : FPdimCategoryData C) : ℝ :=
  D.fpDimCategory

end CategoryTheory
