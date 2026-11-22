/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.DeligneTensorProductDef

open CategoryTheory

namespace TensorCategories

/-- Definition 1.46.1: Deligne's tensor product C ⊠ D is an abelian category which is universal
for the functor assigning to every k-linear abelian category A the category of right exact in both
variables bilinear bifunctors C × D → A. This abbreviation refers to the existence predicate
`Deligne.HasDeligneTensorProduct`. -/
abbrev Definition_1_46_1 := @Deligne.HasDeligneTensorProduct

/-- Predicate that a bifunctor C × D → A is right exact in both variables and bilinear, as required
in the universal property defining Deligne's tensor product in Definition 1.46.1. -/
abbrev IsRightExactBilinearBifunctor_1_46_1 := @Deligne.IsRightExactBilinearBifunctor

end TensorCategories
