/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Ideals

def IsIdeal (R : Type*) [Ring R] (I : Set R) : Prop :=
  (∀ a ∈ I, ∀ b ∈ I, a + b ∈ I) ∧
  (0 ∈ I) ∧
  (∀ a ∈ I, -a ∈ I) ∧
  (∀ a ∈ I, ∀ r : R, r * a ∈ I)

def principalIdeal (R : Type*) [CommRing R] (a : R) : Ideal R :=
  Ideal.span {a}

instance instCommRingQuotient (R : Type*) [CommRing R] (I : Ideal R) :
    CommRing (R ⧸ I) :=
  Ideal.Quotient.commRing I

theorem isMaximal_iff (R : Type*) [CommRing R] (I : Ideal R) :
    I.IsMaximal ↔ (I ≠ ⊤ ∧ ∀ J : Ideal R, I ≤ J → J = I ∨ J = ⊤) := by
  constructor
  · intro hI
    refine ⟨hI.ne_top, fun J hIJ => ?_⟩
    rcases hIJ.eq_or_lt with h | h
    · left; exact h.symm
    · right; exact hI.out.2 J h
  · intro ⟨hne, honly⟩
    constructor
    refine ⟨hne, fun J hIJ => ?_⟩
    rcases honly J (le_of_lt hIJ) with h | h
    · exact absurd hIJ (h ▸ lt_irrefl I)
    · exact h
