/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.SimpleModule.Basic

noncomputable section

namespace TwoSidedIdeal

variable {R : Type*} [Ring R]

def moduleAnnihilator (R : Type*) [Ring R] (M : Type*) [AddCommGroup M]
    [Module R M] : TwoSidedIdeal R :=
  TwoSidedIdeal.mk'
    { r : R | ∀ m : M, r • m = 0 }
    (fun m => zero_smul R m)
    (fun hr hs m => by rw [add_smul, hr m, hs m, add_zero])
    (fun hr m => by rw [neg_smul, hr m, neg_zero])
    (fun {x y} hy m => by rw [mul_smul, hy m, smul_zero])
    (fun {x y} hx m => by rw [mul_smul]; exact hx (y • m))

def IsPrimitive.{u} (I : TwoSidedIdeal R) : Prop :=
  ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M) (_ : IsSimpleModule R M),
    I = moduleAnnihilator R M

end TwoSidedIdeal
