/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Quotient.Basic

universe u v

namespace Lemma34





/-- Helper: `NoZeroSMulDivisors` transfers along a linear equivalence. -/
theorem noZeroSMulDivisors_of_linearEquiv
    {R' : Type*} [CommRing R'] [IsDomain R']
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R' M₁]
    [AddCommGroup M₂] [Module R' M₂] [NoZeroSMulDivisors R' M₂]
    (e : M₁ ≃ₗ[R'] M₂) : NoZeroSMulDivisors R' M₁ where
  eq_zero_or_eq_zero_of_smul_eq_zero {r x} h := by
    have h' : r • e x = 0 := by rw [← e.map_smul, h, map_zero]
    rcases smul_eq_zero.mp h' with hr | hx
    · left; exact hr
    · right; exact e.injective (by rw [hx, map_zero])

/-- Helper: the torsion property transfers along a linear equivalence. -/
lemma Module.IsTorsion.of_linearEquiv {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (h : Module.IsTorsion R N) : Module.IsTorsion R M := by
  intro x
  obtain ⟨⟨a, ha⟩, hax⟩ := h (x := e x)
  refine ⟨⟨a, ha⟩, ?_⟩
  apply e.injective
  simp only [map_zero]
  change e ((a : R) • x) = 0
  rw [map_smul]
  exact hax

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]




end Lemma34

