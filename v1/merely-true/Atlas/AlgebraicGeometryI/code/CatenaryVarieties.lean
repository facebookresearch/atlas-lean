/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.Topology.KrullDimension

open TopologicalSpace Order

/-- A preorder is catenary when any two unrefinable (covering) chains with the same endpoints
have the same length. -/
def IsCatenary (α : Type*) [Preorder α] : Prop :=
  ∀ (s₁ s₂ : LTSeries α),
    s₁.toFun 0 = s₂.toFun 0 →
    s₁.toFun (Fin.last s₁.length) = s₂.toFun (Fin.last s₂.length) →
    (∀ i : Fin s₁.length, s₁.toFun i.castSucc ⋖ s₁.toFun i.succ) →
    (∀ i : Fin s₂.length, s₂.toFun i.castSucc ⋖ s₂.toFun i.succ) →
    s₁.length = s₂.length

/-- A commutative ring is catenary when its prime spectrum is catenary as a preorder. -/
def IsRingCatenary (R : Type*) [CommRing R] : Prop :=
  IsCatenary (PrimeSpectrum R)








