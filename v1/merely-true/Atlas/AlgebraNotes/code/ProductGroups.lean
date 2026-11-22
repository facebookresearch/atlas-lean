/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace ProductGroups

theorem prod_group_mul_def {G H : Type*} [Group G] [Group H]
    (g₁ g₂ : G) (h₁ h₂ : H) :
    (g₁, h₁) * (g₂, h₂) = (g₁ * g₂, h₁ * h₂) := by
  rfl
