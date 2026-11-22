/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannRochGeneral
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

open scoped TensorProduct

noncomputable section

namespace RiemannFormRR

/-- `ℓ(D) := dim_k Hom_A(I, A)`, the dimension of the space of regular sections
of the line bundle attached to a divisor with associated ideal `I`. -/
def lD (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] (I : Ideal A) : ℕ :=
  Module.finrank k (↥I →ₗ[A] A)

/-- `ℓ(K − D) := dim_k Hom_A(I, Ω[A/k])`, the dimension of regular sections of
the differential twist `K − D`, the Serre dual. -/
def lKD (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] (I : Ideal A) : ℕ :=
  Module.finrank k (↥I →ₗ[A] Ω[A⁄k])

/-- The Euler characteristic `ℓ(D) − ℓ(K−D)`, the left-hand side of the
Riemann–Roch formula. -/
def divisorEulerChar (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] (I : Ideal A) : ℤ :=
  (lD k A I : ℤ) - (lKD k A I : ℤ)

/-- Predicate: `A` satisfies Riemann–Roch (Cor 30) — for every nonzero ideal
`I` the Euler characteristic equals `deg D + 1 − g`. -/
def SatisfiesRiemannRoch (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : Prop :=
  ∀ (I : Ideal A), I ≠ ⊥ →
    divisorEulerChar k A I =
      (RiemannRochGeneral.lineBundleDegree k A I : ℤ) + 1 -
      (RiemannRochGeneral.arithmeticGenus k A : ℤ)

/-- Unfolding the Riemann–Roch predicate: extracting the formula at a fixed
nonzero ideal `I`. -/
theorem SatisfiesRiemannRoch.rr_formula {k : Type*} [Field k] {A : Type*} [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A]
    (h : SatisfiesRiemannRoch k A) (I : Ideal A) (hI : I ≠ ⊥) :
    divisorEulerChar k A I =
      (RiemannRochGeneral.lineBundleDegree k A I : ℤ) + 1 -
      (RiemannRochGeneral.arithmeticGenus k A : ℤ) :=
  h I hI

/-- Identification `Hom_A(A, M) ≃ M`: the case `I = ⊤` of the Hom-bundle, used
to compute `ℓ(⊤) = dim_k A`. -/
def homTopEquiv (k : Type*) [Field k] (A : Type*) [CommRing A]
    [Algebra k A] (M : Type*) [AddCommGroup M] [Module A M]
    [Module k M] [SMulCommClass A k M] :
    (↥(⊤ : Ideal A) →ₗ[A] M) ≃ₗ[k] M :=
  (LinearEquiv.congrLeft M k (Submodule.topEquiv (R := A))).trans
    (LinearMap.ringLmapEquivSelf A k M)

/-- `ℓ(⊤) = dim_k A`: trivial-divisor specialization of `lD`. -/
theorem lD_top (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] :
    lD k A ⊤ = Module.finrank k A :=
  LinearEquiv.finrank_eq (homTopEquiv k A A)

/-- `ℓ(K − ⊤) = dim_k Ω[A/k] = g`, the arithmetic genus. -/
theorem lKD_top (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] :
    lKD k A ⊤ = Module.finrank k (Ω[A⁄k]) :=
  LinearEquiv.finrank_eq (homTopEquiv k A (Ω[A⁄k]))

/-- Sanity check: the Riemann–Roch formula holds for the trivial Dedekind
domain `A = k`, where `g = 0`, `deg D = 0`, and Euler characteristic equals
`1 = 0 + 1 − 0`. -/
theorem riemann_roch_field (k : Type*) [Field k] (I : Ideal k) (hI : I ≠ ⊥) :
    @divisorEulerChar k _ k _ _ _ (Algebra.id k) I =
    (@RiemannRochGeneral.lineBundleDegree k _ k _ _ (Algebra.id k) I : ℤ) + 1 -
    (@RiemannRochGeneral.arithmeticGenus k _ k _ _ _ (Algebra.id k) inferInstance : ℤ) := by

  have hItop : I = ⊤ := by
    rcases I.eq_bot_or_top with h | h
    · exact absurd h hI
    · exact h
  subst hItop
  unfold divisorEulerChar lD lKD RiemannRochGeneral.lineBundleDegree RiemannRochGeneral.arithmeticGenus

  haveI hss : Subsingleton (Ω[k⁄k]) :=
    KaehlerDifferential.subsingleton_of_surjective k k (fun x => ⟨x, rfl⟩)
  have hg : Module.finrank k (Ω[k⁄k]) = 0 := Module.finrank_zero_of_subsingleton
  haveI : Subsingleton (k ⧸ (⊤ : Ideal k)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  have hdeg : Module.finrank k (k ⧸ (⊤ : Ideal k)) = 0 := Module.finrank_zero_of_subsingleton
  have hlD : Module.finrank k (↥(⊤ : Ideal k) →ₗ[k] k) = 1 := by
    rw [LinearEquiv.finrank_eq (homTopEquiv k k k), Module.finrank_self]
  haveI : Subsingleton (↥(⊤ : Ideal k) →ₗ[k] Ω[k⁄k]) := by
    constructor; intro f g; ext x; exact Subsingleton.elim _ _
  have hlKD : Module.finrank k (↥(⊤ : Ideal k) →ₗ[k] Ω[k⁄k]) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [hlD, hlKD, hdeg, hg]
  norm_num

end RiemannFormRR
