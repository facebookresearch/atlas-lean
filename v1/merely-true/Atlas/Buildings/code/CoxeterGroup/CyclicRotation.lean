/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Group.List.Lemmas

namespace CoxeterGroup

variable {G : Type*} [Group G]

/-- If the product of a list in a group is the identity, then the product of
any cyclic rotation of that list is also the identity. -/
theorem list_prod_rotate_eq_one {w : List G} (hw : w.prod = 1) (k : ℕ) :
    (w.rotate k).prod = 1 :=
  List.prod_rotate_eq_one_of_prod_eq_one hw k

end CoxeterGroup
