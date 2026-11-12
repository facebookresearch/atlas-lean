/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Atlas.NumberTheoryI.code.Prop1837

open Finset BigOperators
open scoped AddChar ComplexConjugate

namespace CharacterOrthogonality

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem sum_char_ne_zero_iff (χ : AddChar G ℂ) :
    ∑ g : G, χ g ≠ 0 ↔ χ = 0 := by
  classical
  rw [AddChar.sum_eq_ite, ne_eq]
  constructor
  · intro h
    by_contra hne
    simp [hne] at h
  · intro h
    subst h
    simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

theorem sum_dual_ne_zero_iff [DecidableEq G] (g : G) :
    ∑ χ : AddChar G ℂ, χ g ≠ 0 ↔ g = 0 := by
  rw [AddChar.sum_apply_eq_ite, ne_eq]
  constructor
  · intro h
    by_contra hne
    simp [hne] at h
  · intro h
    subst h
    simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

theorem corollary_18_38 [DecidableEq G] :
    (∀ χ : AddChar G ℂ, ∑ g : G, χ g ≠ 0 ↔ χ = 0) ∧
    (∀ g : G, ∑ χ : AddChar G ℂ, χ g ≠ 0 ↔ g = 0) :=
  ⟨sum_char_ne_zero_iff, sum_dual_ne_zero_iff⟩

end CharacterOrthogonality

namespace Cor1838

export CharacterOrthogonality (sum_char_ne_zero_iff sum_dual_ne_zero_iff corollary_18_38)
end Cor1838
