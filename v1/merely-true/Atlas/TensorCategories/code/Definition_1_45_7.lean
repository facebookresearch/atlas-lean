/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FPdimCategory

open CategoryTheory

universe u v

/-- Definition 1.45.7: The regular element R of a transitive unital Z₊-ring A satisfies
XR = FPdim(X) R for all X in A. Here, given the Frobenius-Perron dimension data of a monoidal
category, this returns the categorical Frobenius-Perron dimension (the dimension of the regular
object). -/
noncomputable abbrev Definition_1_45_7 {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (D : FPdimCategoryData C) : ℝ :=
  D.fpDimCategory

/-- Lowercase alias for `Definition_1_45_7`. -/
noncomputable abbrev def_1_45_7 {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (D : FPdimCategoryData C) : ℝ :=
  Definition_1_45_7 D
