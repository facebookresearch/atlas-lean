/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.Isogenies
import Atlas.EllipticCurves.code.PointCounting
import Atlas.EllipticCurves.code.JInvariant
import Atlas.EllipticCurves.code.EndomorphismAlgebra
import Atlas.EllipticCurves.code.EndAlgClassification

import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

universe u

namespace OrdinarySupersingular

variable {F : Type u} [Field F] [DecidableEq F]







/-- The `p`-torsion subgroup of `E`: the set of points `P` killed by multiplication by `p`. -/
def pTorsionSubgroup (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] : Set E.Point :=
  { P | (p : ℤ) • P = 0 }

/-- An elliptic curve `E` over a field of characteristic `p` is supersingular if its `p`-torsion
subgroup is trivial. -/
def IsSupersingular (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] : Prop :=
  ∀ P : E.Point, (p : ℤ) • P = 0 → P = 0

/-- An elliptic curve `E` over a field of characteristic `p` is ordinary if it admits a nonzero
`p`-torsion point. -/
def IsOrdinary (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] : Prop :=
  ∃ P : E.Point, (p : ℤ) • P = 0 ∧ P ≠ 0

/-- `E` is ordinary iff it is not supersingular. -/
theorem isOrdinary_iff_not_supersingular (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] :
    IsOrdinary E p ↔ ¬ IsSupersingular E p := by
  constructor
  · rintro ⟨P, hP, hPne⟩ hss
    exact hPne (hss P hP)
  · intro hns
    unfold IsSupersingular at hns
    push_neg at hns
    exact hns


/-- Every elliptic curve over a field of characteristic `p` is either ordinary or supersingular. -/
theorem ordinary_or_supersingular (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] :
    IsOrdinary E p ∨ IsSupersingular E p := by
  rcases em (IsSupersingular E p) with hss | hns
  · exact Or.inr hss
  · exact Or.inl ((isOrdinary_iff_not_supersingular E p).mpr hns)












omit [DecidableEq F] in
/-- Frobenius compatibility of the `j`-invariant: applying the `p^2`-power Frobenius to the
coefficients `A`, `B` and to the resulting `j`-invariant agree. -/
theorem jInvariant_pow_frobenius (A B : F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] :
    jInvariant (A ^ (p ^ 2)) (B ^ (p ^ 2)) = (jInvariant A B) ^ (p ^ 2) := by
  haveI : ExpChar F p := expChar_prime F p

  let φ := iterateFrobenius F p 2
  have hφ : ∀ x : F, φ x = x ^ (p ^ 2) := fun x => iterateFrobenius_def p 2 x

  suffices h : φ (jInvariant A B) = jInvariant (φ A) (φ B) by
    rw [← hφ (jInvariant A B), h]
    simp only [hφ]

  simp only [jInvariant, φ, map_div₀, map_mul, map_pow, map_add, map_ofNat]






















end OrdinarySupersingular

namespace OrdinarySupersingularClassification

open ConductorOrder

variable {d : ℤ}

/-- If the conductor-`f₁` order is contained in the conductor-`f₂` order, then `f₂ ∣ f₁`. This is
the standard correspondence between containment of orders and divisibility of conductors. -/
theorem conductor_dvd_of_le {f₁ f₂ : ℕ}
    (h : conductorOrder d f₁ ≤ conductorOrder d f₂) :
    f₂ ∣ f₁ := by

  have hmem : (⟨0, (f₁ : ℤ)⟩ : ℤ√d) ∈ conductorOrder d f₂ := by
    apply h
    simp [mem_conductorOrder_iff]

  rw [mem_conductorOrder_iff] at hmem
  exact Int.natCast_dvd_natCast.mp hmem

section EC_Application

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The Frobenius discriminant of `E/F_q`: `t² - 4q`, where `t = tr π_E`. -/
noncomputable def frobDiscriminant (E : WeierstrassCurve.Affine F) : ℤ :=
  (Hasse.traceFrobenius E) ^ 2 - 4 * (Fintype.card F : ℤ)

/-- The predicate that the Frobenius endomorphism is not an integer (i.e., `t² ≠ 4q`), so that
`ℤ[π_E]` is a non-trivial quadratic order. -/
def frobNotInt (E : WeierstrassCurve.Affine F) : Prop :=
  (Hasse.traceFrobenius E) ^ 2 ≠ 4 * (Fintype.card F : ℤ)







end EC_Application

end OrdinarySupersingularClassification
