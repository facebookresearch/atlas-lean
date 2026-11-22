/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.QuotientGroup.Defs

namespace QuotientGroups

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

theorem quotient_group_composition :
    Function.Surjective (QuotientGroup.mk' N) ∧
    MonoidHom.ker (QuotientGroup.mk' N) = N :=
  ⟨QuotientGroup.mk'_surjective N, QuotientGroup.ker_mk' N⟩

end QuotientGroups
