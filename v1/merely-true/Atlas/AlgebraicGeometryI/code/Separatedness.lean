/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Separation.Basic
import Mathlib.RingTheory.Kaehler.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Algebra.TensorProduct MvPolynomial

universe u

namespace Separatedness

/-- Any affine scheme is separated. -/
theorem affine_isSeparated (X : Scheme.{u}) [IsAffine X] : X.IsSeparated :=
  inferInstance

/-- Forward direction of Prop 9 (separatedness via affine opens): in a
separated scheme `X`, the intersection of two affine open subschemes is
affine. -/
theorem prop9_forward
    {X : Scheme.{u}} [X.IsSeparated]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) :=
  hU.inf hV

/-- The diagonal of `X` is an affine morphism iff intersections of affine
opens in `X` are affine. -/
theorem affine_diagonal_iff_affine_intersection
    {X : Scheme.{u}} :
    IsAffineHom (pullback.diagonal (terminal.from X)) ↔
    ∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) := by
  constructor
  · intro h U V hU hV
    haveI := h
    exact hU.inf hV
  · intro h
    rw [isAffineHom_diagonal_iff]
    intro U _ V₁ _ V₂ _ hV₁ hV₂
    exact h V₁ V₂ hV₁ hV₂

/-- Proposition 9 (separatedness criterion): `X` is separated iff
(i) intersections of affine opens are affine, and (ii) the diagonal map
induces surjections on affine open stalks. -/
theorem prop9_separated_iff
    {X : Scheme.{u}} :
    X.IsSeparated ↔
    (∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) ∧
    (∀ (W : (pullback (terminal.from X) (terminal.from X)).Opens),
      IsAffineOpen W →
      Function.Surjective ((pullback.diagonal (terminal.from X)).app W)) := by
  rw [Scheme.isSeparated_iff, isSeparated_iff,
      isClosedImmersion_iff_isAffineHom]
  constructor
  · rintro ⟨hAff, hSurj⟩
    exact ⟨affine_diagonal_iff_affine_intersection.mp hAff, hSurj⟩
  · rintro ⟨hAff, hSurj⟩
    exact ⟨affine_diagonal_iff_affine_intersection.mpr hAff, hSurj⟩

section TensorProductRules

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Tensor product derivation rule for multiplication:
`(ab) ⊗ 1 − 1 ⊗ (ab) = (a ⊗ 1)(b ⊗ 1 − 1 ⊗ b) + (a ⊗ 1 − 1 ⊗ a)(1 ⊗ b)`. -/
lemma tmul_one_sub_one_tmul_mul (a b : A) :
    (a * b) ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] (a * b) =
    (a ⊗ₜ[R] (1 : A)) * (b ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] b) +
    (a ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] a) * ((1 : A) ⊗ₜ[R] b) := by
  simp only [mul_sub, sub_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  abel

/-- Additivity of the `a ↦ a ⊗ 1 − 1 ⊗ a` map. -/
lemma tmul_one_sub_one_tmul_add (a b : A) :
    (a + b) ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] (a + b) =
    (a ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] a) + (b ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] b) := by
  simp [TensorProduct.add_tmul, TensorProduct.tmul_add]; abel

/-- Elements coming from the base ring vanish under
`a ↦ a ⊗ 1 − 1 ⊗ a`. -/
lemma tmul_one_sub_one_tmul_algebraMap (r : R) :
    (algebraMap R A r) ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, sub_eq_zero]
  exact TensorProduct.CompatibleSMul.smul_tmul r 1 1

end TensorProductRules

end Separatedness
