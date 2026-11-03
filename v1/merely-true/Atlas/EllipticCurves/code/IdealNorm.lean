/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

namespace IdealNorm

variable {𝒪 : Type*} [CommRing 𝒪]

/-- The (absolute) norm of an ideal `𝔞` of `𝒪`, defined as the cardinality of the
quotient `𝒪 / 𝔞`. -/
noncomputable def idealNorm (𝔞 : Ideal 𝒪) : ℕ := Submodule.cardQuot 𝔞

/-- The ideal norm equals the cardinality of the quotient ring `𝒪 / 𝔞`. -/
theorem idealNorm_eq_card_quotient (𝔞 : Ideal 𝒪) :
    idealNorm 𝔞 = Nat.card (𝒪 ⧸ 𝔞) :=
  Submodule.cardQuot_apply 𝔞

/-- The norm of the unit ideal `⊤` is `1`. -/
theorem idealNorm_top : idealNorm (⊤ : Ideal 𝒪) = 1 :=
  Submodule.cardQuot_top 𝒪 𝒪

/-- For an infinite ring `𝒪`, the norm of the zero ideal `⊥` is `0`. -/
theorem idealNorm_bot [Infinite 𝒪] : idealNorm (⊥ : Ideal 𝒪) = 0 :=
  Submodule.cardQuot_bot 𝒪 𝒪

/-- For a nonzero ideal `𝔞` in an integral domain that is a finite free `ℤ`-module,
the ideal norm is strictly positive. -/
theorem idealNorm_pos {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [Module.Free ℤ 𝒪] [Module.Finite ℤ 𝒪] (𝔞 : Ideal 𝒪) (h : 𝔞 ≠ ⊥) :
    0 < idealNorm 𝔞 := by
  rw [idealNorm, Submodule.cardQuot_apply, Nat.pos_iff_ne_zero, Nat.card_ne_zero]
  exact ⟨⟨Ideal.Quotient.mk 𝔞 0⟩, Ideal.finiteQuotientOfFreeOfNeBot 𝔞 h⟩

/-- For a nontrivial Dedekind domain `𝒪` that is a free `ℤ`-module, the Mathlib
absolute norm `Ideal.absNorm` agrees with the cardinality-based `idealNorm`. -/
theorem idealNorm_eq_absNorm {𝒪 : Type*} [CommRing 𝒪] [Nontrivial 𝒪]
    [IsDedekindDomain 𝒪] [Module.Free ℤ 𝒪] (𝔞 : Ideal 𝒪) :
    Ideal.absNorm 𝔞 = idealNorm 𝔞 :=
  Ideal.absNorm_apply 𝔞

end IdealNorm
