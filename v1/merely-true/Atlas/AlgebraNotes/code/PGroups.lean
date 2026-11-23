/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.PGroup

namespace PGroups

variable {p : ℕ} [Fact (Nat.Prime p)] {G : Type*} [Group G]

theorem p_group_center_nontrivial [Finite G] (hG : IsPGroup p G) [Nontrivial G] :
    Nontrivial (Subgroup.center G) :=
  IsPGroup.center_nontrivial hG

end PGroups
