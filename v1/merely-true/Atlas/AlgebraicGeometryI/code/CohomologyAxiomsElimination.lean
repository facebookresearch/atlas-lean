/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.ZariskiSheafCohomology
import Atlas.AlgebraicGeometryI.code.H0GlobalSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open ZariskiSheafCohomology

noncomputable section


namespace CohomologyAxiomsElimination

/-- Concrete definition of `h^1(O)` for an affine curve `Spec A` over `k`: the `k`-dimension of
the Kähler differentials `Ω_{A/k}`. -/
def h1_O_defined (k : Type*) [Field k] (A : Type*) [CommRing A]
    [Algebra k A] : ℕ :=
  Module.finrank k (Ω[A⁄k])

/-- Unfolds `h1_O_defined` to its definition as `finrank Ω_{A/k}`. -/
theorem h1_O_defined_eq_genus (k : Type*) [Field k] (A : Type*) [CommRing A]
    [Algebra k A] :
    h1_O_defined k A = Module.finrank k (Ω[A⁄k]) := rfl

/-- On a Dedekind curve, the elimination definition of `h^1(O)` agrees with the official one. -/
theorem h1_O_defined_eq_h1_O (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] :
    h1_O_defined k A = DedekindCurve.h1_O k A := by
  rw [h1_O_defined, DedekindCurve.h1_O_eq_genus]

/-- Concrete definition of `h^1(skyscraper)`: zero, since the cohomology of a skyscraper sheaf
vanishes in positive degree. -/
def h1_sky_defined (_k : Type*) [Field _k] (_A : Type*) : ℕ := 0

/-- `h1_sky_defined` is definitionally zero. -/
theorem h1_sky_defined_eq_zero (k : Type*) [Field k] (A : Type*) :
    h1_sky_defined k A = 0 := rfl

/-- On a Dedekind curve, the elimination definition of `h^1(skyscraper)` agrees with the
official one. -/
theorem h1_sky_defined_eq_h1_sky (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] :
    h1_sky_defined k A = DedekindCurve.h1_sky k A := by
  rw [h1_sky_defined, DedekindCurve.h1_sky_eq_zero]


/-- The `h^1(O)` of the affine spectrum `Spec R`, computed from the abstract sheaf cohomology. -/
def h1_O_sheafH (k : Type*) [Field k] (R : CommRingCat)
    [Module k (sheafCohomology (Scheme.Spec.obj (Opposite.op R)) 1)] : ℕ :=
  specH k (Scheme.Spec.obj (Opposite.op R)) 1

/-- The `h^0(O)` of the affine spectrum `Spec R`, computed from the abstract sheaf cohomology. -/
def h0_O_sheafH (k : Type*) [Field k] (R : CommRingCat)
    [Module k (sheafCohomology (Scheme.Spec.obj (Opposite.op R)) 0)] : ℕ :=
  specH k (Scheme.Spec.obj (Opposite.op R)) 0


/-- The "grounded" Euler characteristic homomorphism `ℤ × ℤ → ℤ` for a Dedekind curve, built
from the concrete `h1_O_defined` and `h1_sky_defined` values. -/
def groundedCohChi {k : Type*} [Field k] (C : DedekindCurve k) : ℤ × ℤ →+ ℤ where
  toFun p := p.1 * (1 - (h1_O_defined k C.A : ℤ)) + p.2 * (1 - (h1_sky_defined k C.A : ℤ))
  map_zero' := by simp
  map_add' := by intro ⟨r₁, d₁⟩ ⟨r₂, d₂⟩; simp; ring

/-- `groundedCohChi C (1, 0) = 1 - g`, recovering the structure sheaf contribution. -/
theorem groundedCohChi_struct {k : Type*} [Field k] (C : DedekindCurve k) :
    groundedCohChi C (1, 0) = 1 - (C.ddGenus : ℤ) := by
  simp [groundedCohChi, h1_O_defined, DedekindCurve.ddGenus]

/-- `groundedCohChi C (0, 1) = 1`, the skyscraper contribution. -/
theorem groundedCohChi_sky {k : Type*} [Field k] (C : DedekindCurve k) :
    groundedCohChi C (0, 1) = 1 := by
  simp [groundedCohChi, h1_sky_defined]

/-- The grounded Euler characteristic agrees with the official one on a Dedekind curve. -/
theorem groundedCohChi_eq_cohChi {k : Type*} [Field k] (C : DedekindCurve k) :
    groundedCohChi C = C.cohChi := by
  ext ⟨r, d⟩
  simp only [groundedCohChi, DedekindCurve.cohChi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  congr 1


/-- `H^0` agrees with global sections (alias). -/
def h0_equiv_sections (X : Scheme) :=
  h0EquivGlobalSections X

/-- Global sections of `O_{Spec R}` are `R` (alias). -/
def specGlobalSections (R : CommRingCat) :=
  globalSections_Spec_iso R


end CohomologyAxiomsElimination

end
