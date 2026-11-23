/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.Topology.Sheaves.Stalks

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

noncomputable section

namespace Lec6.RegularFunctions

/-- Unfolding `StructureSheaf.IsFraction`: a section is a fraction iff it is
globally given by `g/h` for some `g, h ∈ R` with `h` invertible at every point
of `U`. -/
theorem isFraction_iff (R : Type*) [CommRing R] {U : Opens (PrimeSpectrum.Top R)}
    (f : Π x : U, StructureSheaf.Localizations R x.1) :
    StructureSheaf.IsFraction f ↔
      ∃ (g : R) (h : R), ∀ x : U,
        ∃ (hx : h ∉ x.1.asIdeal), f x = LocalizedModule.mk g ⟨h, hx⟩ := by
  rfl

/-- The stalk of a presheaf at a point is, by definition, the filtered colimit
of its sections over open neighborhoods of that point. -/
theorem stalk_eq_colimit {X : TopCat} (F : X.Presheaf CommRingCat) (x : X) :
    F.stalk x = (TopCat.Presheaf.stalkFunctor CommRingCat x).obj F := rfl

/-- The stalk of the structure sheaf of `Spec R` at a prime `𝔭` is canonically
the localization of `R` at `𝔭`. -/
def stalk_iso_localization (R : Type*) [CommRing R] (𝔭 : PrimeSpectrum R) :
    Localization.AtPrime 𝔭.asIdeal ≃ₐ[R]
      ↑((structurePresheafInCommRingCat R).stalk 𝔭) :=
  StructureSheaf.stalkIso R 𝔭

/-- For an irreducible scheme, the function field is defined as the stalk of
the structure sheaf at the (unique) generic point. -/
theorem functionField_eq_stalk_genericPoint (X : Scheme) [IrreducibleSpace X] :
    X.functionField = X.presheaf.stalk (genericPoint X) := rfl

/-- On an integral scheme, the germ map from sections over a nonempty open `U`
into the function field is injective. -/
theorem functionField_germ_injective' (X : Scheme) [IsIntegral X]
    (U : X.Opens) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) :=
  Scheme.germToFunctionField_injective X U

/-- The function field of an integral scheme is a field. -/
instance functionField_field' (X : Scheme) [IsIntegral X] :
    Field X.functionField := inferInstance

end Lec6.RegularFunctions
