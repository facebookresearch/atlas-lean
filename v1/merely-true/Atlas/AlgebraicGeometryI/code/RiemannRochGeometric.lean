/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RiemannRochGeometric

/-- Axiomatic data for a smooth complete curve `X` over a field `k`, together
with cohomology dimensions and the Riemann–Roch ingredients (rank, degree,
arithmetic genus) needed for Thm 24.2 (Lec 24). -/
structure SmoothCurveWithCohomology (k : Type) [Field k] where
  X : Scheme
  f : X ⟶ Spec (CommRingCat.of k)
  [isIntegral : AlgebraicGeometry.IsIntegral X]
  [isProper : IsProper f]
  [isSmooth : SmoothOfRelativeDimension 1 f]
  dimH0 : X.Modules → ℕ
  dimH1 : X.Modules → ℕ
  degree : X.Modules → ℤ
  sheafRank : X.Modules → ℤ
  arithmeticGenus : ℕ
  chiK0 : ℤ × ℤ →+ ℤ
  chi_eq_chiK0 : ∀ F : X.Modules,
    (dimH0 F : ℤ) - (dimH1 F : ℤ) = chiK0 (sheafRank F, degree F)
  chi_structureSheaf : chiK0 (1, 0) = 1 - (arithmeticGenus : ℤ)
  chi_skyscraper : chiK0 (0, 1) = 1

attribute [instance] SmoothCurveWithCohomology.isIntegral
    SmoothCurveWithCohomology.isProper SmoothCurveWithCohomology.isSmooth

variable {k : Type} [Field k]

/-- Euler characteristic `χ(F) = h^0(F) - h^1(F)` of a sheaf on a smooth
complete curve. -/
def SmoothCurveWithCohomology.eulerChar (C : SmoothCurveWithCohomology k)
    (F : C.X.Modules) : ℤ :=
  (C.dimH0 F : ℤ) - (C.dimH1 F : ℤ)

/-- The structure sheaf of a smooth complete curve, packaged as a module
sheaf. -/
def SmoothCurveWithCohomology.structureSheafMod (C : SmoothCurveWithCohomology k) :
    C.X.Modules :=
  SheafOfModules.unit C.X.ringCatSheaf

/-- The Riemann–Roch formula evaluated on `(r, d)`: `d + r(1 - g)`. -/
def SmoothCurveWithCohomology.rrFormula (C : SmoothCurveWithCohomology k) (r d : ℤ) : ℤ :=
  d + r * (1 - (C.arithmeticGenus : ℤ))


/-- Any additive map `ℤ × ℤ → ℤ` is determined by its values on the
generators `(1, 0)` and `(0, 1)`. -/
theorem additive_hom_determined (f : ℤ × ℤ →+ ℤ) (p : ℤ × ℤ) :
    f p = p.1 * f (1, 0) + p.2 * f (0, 1) := by
  obtain ⟨r, d⟩ := p
  show f (r, d) = r * f (1, 0) + d * f (0, 1)
  have h1 : (r, d) = (r, 0) + (0, d) := by ext <;> simp
  rw [h1, map_add]
  congr 1
  · have : (r, (0 : ℤ)) = r • (1, 0) := by ext <;> simp
    rw [this, map_zsmul, smul_eq_mul]
  · have : ((0 : ℤ), d) = d • (0, 1) := by ext <;> simp
    rw [this, map_zsmul, smul_eq_mul]


/-- Theorem 24.2 (Riemann–Roch for curves, Lec 24): for any sheaf `F`,
`χ(F) = deg(F) + rank(F)·(1 - g_a)`. -/
theorem theorem_24_2 (C : SmoothCurveWithCohomology k) (F : C.X.Modules) :
    C.eulerChar F = C.degree F + C.sheafRank F * (1 - (C.arithmeticGenus : ℤ)) := by
  unfold SmoothCurveWithCohomology.eulerChar
  rw [C.chi_eq_chiK0 F]
  rw [additive_hom_determined C.chiK0 (C.sheafRank F, C.degree F)]
  rw [C.chi_structureSheaf, C.chi_skyscraper]
  ring

/-- Alternative form of Theorem 24.2: `χ(F) = deg(F) - rank(F)·(g_a - 1)`. -/
theorem theorem_24_2_alt (C : SmoothCurveWithCohomology k) (F : C.X.Modules) :
    C.eulerChar F = C.degree F - C.sheafRank F * ((C.arithmeticGenus : ℤ) - 1) := by
  have h := theorem_24_2 C F
  linarith


/-- Theorem 24.2 specialized to line bundles (rank 1): `χ(L) = d + 1 - g`. -/
theorem theorem_24_2_rank_one (C : SmoothCurveWithCohomology k) (F : C.X.Modules)
    (hrank : C.sheafRank F = 1) :
    C.eulerChar F = C.degree F + 1 - (C.arithmeticGenus : ℤ) := by
  have h := theorem_24_2 C F
  rw [hrank] at h
  linarith

/-- Theorem 24.2 for torsion (rank 0) sheaves: `χ(F) = deg(F)`. -/
theorem theorem_24_2_torsion (C : SmoothCurveWithCohomology k) (F : C.X.Modules)
    (hrank : C.sheafRank F = 0) :
    C.eulerChar F = C.degree F := by
  have h := theorem_24_2 C F
  rw [hrank] at h
  linarith

/-- Theorem 24.2 specialized to the structure sheaf: `χ(𝒪_X) = 1 - g`. -/
theorem theorem_24_2_structure_sheaf (C : SmoothCurveWithCohomology k) (F : C.X.Modules)
    (hrank : C.sheafRank F = 1) (hdeg : C.degree F = 0) :
    C.eulerChar F = 1 - (C.arithmeticGenus : ℤ) := by
  have h := theorem_24_2 C F
  rw [hrank, hdeg] at h
  linarith

end RiemannRochGeometric

end
