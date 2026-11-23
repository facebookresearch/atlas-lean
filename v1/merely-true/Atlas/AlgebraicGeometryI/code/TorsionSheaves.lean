/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.TorsionSheaf

variable {X : Scheme.{u}}

/-- A section `s` of a sheaf of `O_X`-modules `F` over `U` is a torsion
section iff it is annihilated by some nonzero scalar in `O_X(U)`. -/
def IsTorsionSection (F : X.Modules) (U : X.Opens)
    (s : (Scheme.Modules.presheaf F).obj (.op U)) : Prop :=
  ∃ r : X.presheaf.obj (.op U), r ≠ 0 ∧ r • s = 0

/-- A sheaf of `O_X`-modules is torsion iff every section over every
nonempty open is a torsion section. -/
def IsTorsionSheaf (F : X.Modules) : Prop :=
  ∀ (U : X.Opens) [Nonempty U] (s : (Scheme.Modules.presheaf F).obj (.op U)),
    IsTorsionSection F U s

/-- A sheaf of `O_X`-modules is torsion-free iff its only torsion section over
any nonempty open is the zero section. -/
def IsTorsionFreeSheaf (F : X.Modules) : Prop :=
  ∀ (U : X.Opens) [Nonempty U] (s : (Scheme.Modules.presheaf F).obj (.op U)),
    IsTorsionSection F U s → s = 0

section IntegralScheme

variable [IsIntegral X]

/-- On an integral scheme, being a torsion section coincides with membership
in the torsion submodule of the sections, since `O_X(U)` is a domain. -/
lemma isTorsionSection_iff_mem_torsion (F : X.Modules) (U : X.Opens) [Nonempty U]
    (s : (Scheme.Modules.presheaf F).obj (.op U)) :
    IsTorsionSection F U s ↔
      s ∈ Submodule.torsion (X.presheaf.obj (.op U))
        ((Scheme.Modules.presheaf F).obj (.op U)) := by
  constructor
  · rintro ⟨r, hr, hrs⟩
    exact ⟨⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr⟩, hrs⟩
  · rintro ⟨⟨r, hr⟩, hrs⟩
    exact ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, hrs⟩

/-- The submodule of torsion sections of `F` over `U`. -/
noncomputable def torsionSections (F : X.Modules) (U : X.Opens) :
    Submodule (X.presheaf.obj (.op U)) ((Scheme.Modules.presheaf F).obj (.op U)) :=
  Submodule.torsion (X.presheaf.obj (.op U)) ((Scheme.Modules.presheaf F).obj (.op U))

/-- Membership in `torsionSections F U` is the same as being a torsion
section. -/
@[simp]
lemma mem_torsionSections_iff (F : X.Modules) (U : X.Opens) [Nonempty U]
    (s : (Scheme.Modules.presheaf F).obj (.op U)) :
    s ∈ torsionSections F U ↔ IsTorsionSection F U s :=
  (isTorsionSection_iff_mem_torsion F U s).symm

/-- A sheaf is torsion-free iff the torsion submodule of its sections is zero
on every nonempty open. -/
lemma isTorsionFreeSheaf_iff_torsionSections_eq_bot (F : X.Modules) :
    IsTorsionFreeSheaf F ↔
      ∀ (U : X.Opens) [Nonempty U], torsionSections F U = ⊥ := by
  constructor
  · intro hF U _
    ext s
    simp only [mem_torsionSections_iff, Submodule.mem_bot]
    exact ⟨hF U s, fun h => by subst h; exact ⟨1, one_ne_zero, smul_zero 1⟩⟩
  · intro hF U _ s hs
    rw [← Submodule.mem_bot (R := X.presheaf.obj (.op U)),
        ← hF U, mem_torsionSections_iff]
    exact hs

end IntegralScheme


end AlgebraicGeometry.TorsionSheaf
