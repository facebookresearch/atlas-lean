/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CechCohomologyIdentification
import Atlas.AlgebraicGeometryI.code.GenusConstruction

noncomputable section

universe v

namespace CechSheafDataP1

open SerreDualityTate CanonicalSheafCurves GenusConstruction
open TateCechInfra

variable (k : Type) [Field k]


/-- The Tate duality setup for `P¹` with its standard two-open cover: the ambient `k`-vector
space is `k` itself with both subspaces equal to the top subspace. -/
def tateSetupP1 : TateDualitySetup k where
  V := k
  V₁ := ⊤
  V₂ := ⊤

instance : FiniteDimensional k (tateSetupP1 k).V :=
  inferInstanceAs (FiniteDimensional k k)


/-- For the standard two-open cover of `P¹`, the first Čech cohomology of the structure sheaf
vanishes. -/
lemma finrank_cechH1_eq_zero :
    Module.finrank k (tateSetupP1 k).cechH1 = 0 := by

  show Module.finrank k ((tateSetupP1 k).V ⧸ ((tateSetupP1 k).V₁ ⊔ (tateSetupP1 k).V₂)) = 0
  have h_top : (tateSetupP1 k).V₁ ⊔ (tateSetupP1 k).V₂ = ⊤ := by
    show (⊤ : Submodule k k) ⊔ ⊤ = ⊤
    exact sup_idem _
  rw [h_top]

  show Module.finrank k (k ⧸ (⊤ : Submodule k k)) = 0
  have h := Submodule.finrank_quotient_add_finrank (⊤ : Submodule k k)
  rw [finrank_top k k] at h
  omega

/-- For the standard cover of `P¹`, the 0-th Čech cohomology of the dual setup also vanishes. -/
lemma finrank_dual_cechH0_eq_zero :
    Module.finrank k ↥(tateSetupP1 k).dual.cechH0 = 0 := by

  unfold tateSetupP1 TateDualitySetup.dual TateDualitySetup.cechH0
  simp only

  have h_top_ann : (⊤ : Submodule k k).dualAnnihilator = ⊥ :=
    Submodule.dualAnnihilator_top
  rw [h_top_ann]
  simp


/-- The smooth complete curve `P¹` constructed from the Čech data. -/
def P1 : SmoothCompleteCurve := P1CurveFromCech k

/-- The genus of `P¹` is `0`. -/
lemma P1_genus : (P1 k).g = 0 := P1CurveFromCech_genus k
/-- The degree of the canonical bundle of `P¹` is `-2`. -/
lemma P1_degK : (P1 k).degK = -2 := P1CurveFromCech_degK k

/-- The Euler characteristic of the structure sheaf of `P¹` is `1`. -/
lemma P1_chi_O : (P1 k).χ (1, 0) = 1 := by
  exact (P1 k).hχ_struct














end CechSheafDataP1

end
