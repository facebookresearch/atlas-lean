/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.TateCohomology
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic

noncomputable section

universe u

namespace TateCohomology

open Finset CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

instance tateH0.inhabited (A : Rep k G) : Inhabited (tateH0 A) := ⟨0⟩

instance tateMinus1.inhabited (A : Rep k G) : Inhabited (tateMinus1 A) := ⟨0⟩

theorem herbrandQuotient_eq_one_of_finite' [IsCyclic G] (A : Rep k G)
    [Finite A] [Fintype (tateH0 A)] [Fintype (tateMinus1 A)] :
    herbrandQuotient A = 1 := by
  have heq := herbrand_quotient_eq_one_of_finite A
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at heq
  unfold herbrandQuotient
  rw [heq]
  have hpos : (0 : ℚ) < Fintype.card (tateMinus1 A) := by
    exact_mod_cast Fintype.card_pos (α := tateMinus1 A)
  exact div_self hpos.ne'

instance tateH0.finite (A : Rep k G) [Finite A] : Finite (tateH0 A) := by
  unfold tateH0
  haveI : Finite A.ρ.invariants :=
    Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  exact Finite.of_surjective (Submodule.Quotient.mk (p := normImageInInvariants A))
    (Submodule.Quotient.mk_surjective _)

instance tateMinus1.finite (A : Rep k G) [Finite A] : Finite (tateMinus1 A) := by
  unfold tateMinus1
  haveI : Finite (LinearMap.ker (normMap k G A)) :=
    Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  exact Finite.of_surjective (Submodule.Quotient.mk (p := augInKerNorm A))
    (Submodule.Quotient.mk_surjective _)

set_option checkBinderAnnotations false in
theorem finite_of_shortExact_torsion_fg {G₀ : Type} [Group G₀] [Fintype G₀]
    {S : ShortComplex (Rep ℤ G₀)} (hS : S.ShortExact)
    (htors : Module.IsTorsion ℤ S.X₁) (hfg : Module.Finite ℤ S.X₂) :
    Finite (S.X₁ : Rep ℤ G₀) := by

  let φ : ↑S.X₁ →+ ↑S.X₂ :=
    { toFun := S.f.hom
      map_zero' := by simp [map_zero]
      map_add' := by simp [map_add] }

  let ψ : ↑S.X₁ →ₗ[ℤ] ↑S.X₂ := φ.toIntLinearMap

  have hinj : Function.Injective ψ := by
    intro a b hab
    have := hS.mono_f
    exact (Rep.mono_iff_injective S.f).mp this hab

  haveI : IsNoetherian ℤ S.X₂ := isNoetherian_of_isNoetherianRing_of_finite ℤ (↑S.X₂)

  haveI : Module.Finite ℤ S.X₁ := Module.Finite.of_injective ψ hinj

  exact Module.finite_of_fg_torsion _ htors



end TateCohomology
