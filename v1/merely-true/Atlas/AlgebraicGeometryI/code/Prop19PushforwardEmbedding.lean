/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Modules.Sheaf

namespace Prop19

/-- Reformulation: an ideal `I` annihilates a module `M` iff each element of `I` acts
as zero on every element of `M`. -/
theorem pushforward_characterization
    {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    I ≤ Module.annihilator R M ↔ ∀ (r : R) (m : M), r ∈ I → r • m = 0 := by
  constructor
  · intro h r m hr
    exact (Module.mem_annihilator.mp (h hr)) m
  · intro h r hr
    exact Module.mem_annihilator.mpr (fun m => h r m hr)

open CategoryTheory in
/-- Algebraic version of Proposition 19: restriction of scalars along `R → R/I` is a
full and faithful functor from `Mod(R/I)` into `Mod(R)`. -/
theorem pushforward_fullyFaithful (R : Type*) [CommRing R] (I : Ideal R) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).Full ∧
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).Faithful := by
  refine ⟨?_, inferInstance⟩
  constructor
  intro M N g
  refine ⟨ModuleCat.ofHom ⟨g.hom.toAddHom, ?_⟩, ?_⟩
  ·

    intro s m
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact g.hom.map_smul r m
  · ext x; rfl

open CategoryTheory in
/-- Essential image (algebraic version): an `R`-module is a restriction of scalars of an
`R/I`-module iff every element of `I` annihilates `M`. -/
theorem essential_image (R : Type*) [CommRing R] (I : Ideal R)
    (M : ModuleCat R) :
    (∃ (N : ModuleCat (R ⧸ I)), Nonempty ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N ≅ M)) ↔
    ∀ (r : R) (m : M), r ∈ I → r • m = 0 := by
  constructor
  ·
    rintro ⟨N, ⟨iso⟩⟩ r m hr

    have key : r • (iso.inv.hom m) = (0 : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N) := by
      change (Ideal.Quotient.mk I r) • (iso.inv.hom m : N) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
    have h1 := iso.hom.hom.map_smul r (iso.inv.hom m)
    rw [key, map_zero] at h1
    have h2 : iso.hom.hom (iso.inv.hom m) = m := by
      change (iso.inv ≫ iso.hom).hom m = m
      simp [iso.inv_hom_id]
    rw [h2] at h1; exact h1.symm
  ·
    intro hann
    have htors : Module.IsTorsionBySet R M (I : Set R) := by
      intro m ⟨a, ha⟩; exact hann a m ha
    letI := htors.module
    let N : ModuleCat (R ⧸ I) := ModuleCat.of (R ⧸ I) M
    refine ⟨N, ⟨?_⟩⟩


    exact { hom := ModuleCat.ofHom LinearMap.id, inv := ModuleCat.ofHom LinearMap.id,
            hom_inv_id := by ext; rfl, inv_hom_id := by ext; rfl }

section SchemeLevel

open AlgebraicGeometry CategoryTheory

universe u



end SchemeLevel

end Prop19
