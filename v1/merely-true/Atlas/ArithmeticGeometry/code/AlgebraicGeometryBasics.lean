/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.SetTheory.Cardinal.ENat

open Cardinal

noncomputable section

universe u v w w'

variable {ι : Type*}

/-- Any two transcendence bases of a field extension $L/k$ have the same cardinality (up to universe lifts). -/
theorem transcendence_basis_lift_cardinalMk_eq
    {k : Type*} {L : Type*} [Field k] [Field L] [Algebra k L]
    {ι : Type u} {ι' : Type v}
    {x : ι → L} {y : ι' → L}
    (hx : IsTranscendenceBasis k x) (hy : IsTranscendenceBasis k y) :
    Cardinal.lift.{v, u} (Cardinal.mk ι) = Cardinal.lift.{u, v} (Cardinal.mk ι') :=
  hx.lift_cardinalMk_eq hy


/-- The transcendence degree of a field extension $L/k$: the cardinality of any transcendence basis. -/
abbrev transcendenceDegree (k L : Type*) [Field k] [Field L] [Algebra k L] : Cardinal :=
  Algebra.trdeg k L


end

open Order

/-- The Krull dimension of a commutative semiring: the supremum of lengths of chains of prime ideals. -/
noncomputable abbrev krullDimension (R : Type*) [CommSemiring R] : WithBot ℕ∞ :=
  ringKrullDim R


