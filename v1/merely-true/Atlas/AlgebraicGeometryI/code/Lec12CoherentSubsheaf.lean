/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian

section CoherentSubsheaf

/-- Over a Noetherian ring, any submodule of a finitely generated module is itself
finitely generated. -/
theorem submodule_fg_of_noetherian_fg
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) : N.FG :=
  IsNoetherian.noetherian N

/-- Lec 12 (coherent subsheaves): over a Noetherian ring, any submodule of a finitely
presented module is again finitely presented, the algebraic analogue of "a subsheaf of
a coherent sheaf is coherent". -/
theorem subsheaf_coherent_of_noetherian
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    (hM : Module.FinitePresentation R M)
    (N : Submodule R M) : Module.FinitePresentation R N := by

  have hfin : Module.Finite R M := (Module.finitePresentation_iff_finite R M).mp hM


  have hNfg : N.FG := submodule_fg_of_noetherian_fg R M N

  exact (Module.finitePresentation_iff_finite R N).mpr ⟨(Submodule.fg_top _).mpr hNfg⟩

end CoherentSubsheaf
