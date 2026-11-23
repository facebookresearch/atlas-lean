/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs

set_option autoImplicit false

section Prop23

variable (k : Type*) [Field k]

/-- The formal power series ring `k[[x_1, ..., x_n]]` over a field is a domain. -/
instance mvPowerSeries_fin_isDomain' (n : ℕ) : IsDomain (MvPowerSeries (Fin n) k) :=
  NoZeroDivisors.to_isDomain _





end Prop23
