/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CohomologyConnection

noncomputable section

open CategoryTheory CategoryTheory.Limits
open SheafCohomology CohomologyP1 DerivedFunctorsDefs


namespace DerivedFunctorsDefs

universe v₀ u₀

variable {C : Type u₀} [Category.{v₀} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

/-- The identity morphism on a cohomological delta functor. -/
def CohomDeltaFunctor.idMorphism (F : CohomDeltaFunctor C D) : F.Morphism F where
  η n := 𝟙 (F.T n)
  comm_δ n S hS := by simp

/-- The `n`-th component of the identity morphism on a cohomological delta functor is the
identity. -/
@[simp]
theorem CohomDeltaFunctor.idMorphism_η (F : CohomDeltaFunctor C D) (n : ℕ) :
    F.idMorphism.η n = 𝟙 (F.T n) := rfl

end DerivedFunctorsDefs


namespace CohomologyConnection

section RightDerivedEffaceability

universe v₂ u₂

variable {C' : Type u₂} [Category.{v₂} C'] [Abelian C'] [EnoughInjectives C']
         {D' : Type*} [Category D'] [Abelian D']

/-- For any additive functor on a category with enough injectives, the right derived functors of
positive degree are effaceable: each object embeds into an injective whose higher derived images
vanish. -/
theorem rightDerived_effaceable_at
    (F : C' ⥤ D') [F.Additive] (n : ℕ) (X : C') :
    ∃ (I : C') (i : X ⟶ I), Mono i ∧ IsZero ((F.rightDerived (n + 1)).obj I) := by
  obtain ⟨pres⟩ := EnoughInjectives.presentation X
  exact ⟨pres.J, pres.f, pres.mono, F.isZero_rightDerived_obj_injective_succ n pres.J⟩

end RightDerivedEffaceability


section P1Witness

/-- Witness data packaging the basic facts about Čech-versus-derived cohomology of line bundles
on `P¹`: vanishing of `H¹` for nonnegative twists, the Euler characteristic formula, an
effaceability witness, and Serre duality. -/
structure CechToDerivedDataP1Witness (k : Type) [Field k] where
  h1_vanishing : ∀ n : ℤ, 0 ≤ n → Module.finrank k (H1 k n) = 0
  euler_char : ∀ n : ℤ,
    (Module.finrank k (H0 k n) : ℤ) -
    (Module.finrank k (H1 k n) : ℤ) = n + 1
  effaceability : ∀ n : ℤ,
    ∃ N : ℤ, 0 ≤ N ∧ n ≤ N ∧ Module.finrank k (H1 k N) = 0
  serre_duality : ∀ n : ℤ,
    Module.finrank k (H1 k n) =
    Module.finrank k (H0 k (-2 - n))

variable (k : Type) [Field k]

/-- Concrete construction of the `CechToDerivedDataP1Witness` for `P¹` over `k`, drawing on the
`SheafCohomology` and `SheafCohDerived` lemmas. -/
def mkCechToDerivedDataP1Witness : CechToDerivedDataP1Witness k where
  h1_vanishing := SheafCohomology.finrank_H1_of_nonneg k
  euler_char := SheafCohomology.euler_characteristic k
  effaceability := SheafCohDerived.cech_effaceability_witness k
  serre_duality := SheafCohDerived.serre_duality_derived k

/-- The effaceability witness extracted from the assembled `P¹` Čech-to-derived data. -/
theorem p1_witness_effaceability_confirmed (n : ℤ) :
    ∃ N : ℤ, 0 ≤ N ∧ n ≤ N ∧
      Module.finrank k (SheafCohomology.H1 k N) = 0 :=
  (mkCechToDerivedDataP1Witness k).effaceability n

/-- The Euler characteristic identity `h⁰(O(n)) - h¹(O(n)) = n + 1` on `P¹`, packaged through
the witness. -/
theorem p1_witness_euler_confirmed (n : ℤ) :
    (Module.finrank k (SheafCohomology.H0 k n) : ℤ) -
    (Module.finrank k (SheafCohomology.H1 k n) : ℤ) = n + 1 :=
  (mkCechToDerivedDataP1Witness k).euler_char n

end P1Witness

end CohomologyConnection
