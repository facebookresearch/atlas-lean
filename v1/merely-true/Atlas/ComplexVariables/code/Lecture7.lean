/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic

open Complex

structure MoebiusTrans where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

namespace MoebiusTrans

noncomputable def eval (S : MoebiusTrans) (z : ℂ) : ℂ :=
  (S.a * z + S.b) / (S.c * z + S.d)

def IsFixedPoint (S : MoebiusTrans) (z : ℂ) : Prop :=
  S.c * z + S.d ≠ 0 ∧ S.eval z = z

def IsFixedPointAtInfty (S : MoebiusTrans) : Prop := S.c = 0

def IsIdentity (S : MoebiusTrans) : Prop :=
  ∀ z : ℂ, S.c * z + S.d ≠ 0 → S.eval z = z

def HasExactlyOneExtFixedPoint (S : MoebiusTrans) : Prop :=
  (S.IsFixedPointAtInfty ∧ ∀ z : ℂ, ¬S.IsFixedPoint z) ∨
  (¬S.IsFixedPointAtInfty ∧ ∃! z, S.IsFixedPoint z)

def IsParabolic (S : MoebiusTrans) : Prop :=
  S.IsIdentity ∨ S.HasExactlyOneExtFixedPoint

end MoebiusTrans
