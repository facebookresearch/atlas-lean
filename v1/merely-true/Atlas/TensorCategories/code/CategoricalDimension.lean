/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.PivotalSpherical

set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory MonoidalCategory Category Limits

universe v u

namespace TensorCategories

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [PivotalCategory C]

end TensorCategories
