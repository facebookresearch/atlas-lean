/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Module

namespace SubmoduleDirectSum

theorem sup_eq_top_of_finrank_add_eq_and_inf_eq_bot
    {F : Type*} {V : Type*} [DivisionRing F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (W W' : Submodule F V)
    (hdim : finrank F W + finrank F W' = finrank F V)
    (hinter : W ⊓ W' = ⊥) :
    W ⊔ W' = ⊤ := by
  have hd : Disjoint W W' := disjoint_iff.mpr hinter
  exact Submodule.eq_top_of_disjoint W W' (le_of_eq hdim.symm) hd

end SubmoduleDirectSum
