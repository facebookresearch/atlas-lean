/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FrobeniusPerron
import Atlas.TensorCategories.code.GrothendieckRingCategorical
import Atlas.TensorCategories.code.TensorCategoryDef

open CategoryTheory MonoidalCategory
open TensorCategories

universe v u

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : FusionRing ι}

namespace FPdimData

variable (fpd : R.FPdimData)

/-- A Frobenius-Perron dimension datum on a fusion ring is integral if every basis element
has integer Frobenius-Perron dimension. -/
def IsIntegral : Prop :=
  ∀ i : ι, ∃ n : ℤ, fpd.d i = (n : ℝ)

end FPdimData

end FusionRing

/-- A tensor category (equipped with `CategoricalFusionData`) is called integral if its
associated Frobenius-Perron dimension datum on the Grothendieck fusion ring is integral. -/
def IsIntegralTensorCategory
    {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear κ C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
    [RigidCategory C]
    [cfd : CategoricalFusionData κ C]
    (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData) : Prop :=
  fpd.IsIntegral

