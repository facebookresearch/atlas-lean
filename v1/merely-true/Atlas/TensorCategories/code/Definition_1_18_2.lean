/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FiniteAbelianCategoryDef

open CategoryTheory

universe v u

/-- Definition 1.18.2: A k-linear abelian category C is finite if (i) C has finite dimensional
spaces of morphisms; (ii) every object of C has finite length; (iii) C has enough projectives,
i.e., every simple object of C has a projective cover; and (iv) there are finitely many isomorphism
classes of simple objects. This is an alias for `IsFiniteAbelianCategory`. -/
abbrev Definition_1_18_2_IsFiniteAbelianCategory := @CategoryTheory.IsFiniteAbelianCategory
