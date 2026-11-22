/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FiniteAbelianCategoryDef

open CategoryTheory

universe v u

/-- Definition 1.18.1: A k-linear abelian category C is finite if it is equivalent to the
category A-mod of finite dimensional modules over a finite dimensional k-algebra A.
This is an alias for the underlying `Definition_1_18_1_FiniteCategory` predicate. -/
def Definition_1_18_1_FiniteAbelianCategory := @CategoryTheory.Definition_1_18_1_FiniteCategory
