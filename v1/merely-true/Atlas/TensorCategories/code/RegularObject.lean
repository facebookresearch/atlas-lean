/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-- A formal real-coefficient combination of objects indexed by `I`, used to
represent formal sums of projective covers in the Grothendieck setting. -/
abbrev FormalProjectiveSum (I : Type*) := I →₀ ℝ

namespace FormalProjectiveSum

variable {I : Type*}

/-- The coefficient of basis element `i` in the formal sum `s`. -/
def coeff (s : FormalProjectiveSum I) (i : I) : ℝ := s i

/-- The standard basis element of `FormalProjectiveSum I` associated to `i`,
namely the indicator function supported at `i` with value `1`. -/
noncomputable def basis (i : I) : FormalProjectiveSum I :=
  Finsupp.single i 1

/-- The Frobenius–Perron dimension of a formal projective sum `s`, given the
Frobenius–Perron dimensions `fpDimP` of the basis projectives. -/
noncomputable def fpdim [Fintype I] (s : FormalProjectiveSum I) (fpDimP : I → ℝ) : ℝ :=
  ∑ i : I, s.coeff i * fpDimP i

/-- Promote a function `I → ℝ` on a finite type to a `FormalProjectiveSum I`. -/
noncomputable def ofFun [Fintype I] (f : I → ℝ) : FormalProjectiveSum I :=
  Finsupp.equivFunOnFinite.symm f

end FormalProjectiveSum

/-- Frobenius–Perron data for a finite tensor category: a nonempty finite
indexing type `I` of simple objects, together with the (strictly positive)
Frobenius–Perron dimensions of the simples and of their projective covers. -/
structure FiniteTensorCategoryFPData where
  I : Type*
  [I_fintype : Fintype I]
  [I_nonempty : Nonempty I]
  fpDimSimple : I → ℝ
  fpDimProjCover : I → ℝ
  fpDimSimple_pos : ∀ i : I, fpDimSimple i > 0
  fpDimProjCover_pos : ∀ i : I, fpDimProjCover i > 0

attribute [instance] FiniteTensorCategoryFPData.I_fintype
  FiniteTensorCategoryFPData.I_nonempty

namespace FiniteTensorCategoryFPData

variable (D : FiniteTensorCategoryFPData)

/-- The regular object of a finite tensor category: the formal sum of the
projective covers weighted by the Frobenius–Perron dimensions of the simples. -/
noncomputable def regularObject : FormalProjectiveSum D.I :=
  ∑ i : D.I, D.fpDimSimple i • FormalProjectiveSum.basis i

/-- The coefficient of the regular object at `i` equals the Frobenius–Perron
dimension of the simple object `i`. -/
@[simp]
theorem regularObject_coeff (i : D.I) :
    D.regularObject.coeff i = D.fpDimSimple i := by
  classical
  simp [regularObject, FormalProjectiveSum.coeff, FormalProjectiveSum.basis, Finsupp.single_apply]

/-- The Frobenius–Perron dimension of the regular object: the formal sum of
`dim(simple i) · dim(projCover i)`. -/
noncomputable def fpdimRegularObject : ℝ :=
  D.regularObject.fpdim D.fpDimProjCover

/-- The Frobenius–Perron dimension of the regular object expanded as the explicit
sum `∑ dim(simple i) · dim(projCover i)`. -/
theorem fpdimRegularObject_eq :
    D.fpdimRegularObject = ∑ i : D.I, D.fpDimSimple i * D.fpDimProjCover i := by
  simp [fpdimRegularObject, FormalProjectiveSum.fpdim]

end FiniteTensorCategoryFPData

/-- Reference abbreviation for Definition 1.47.4 (the regular object of a finite
tensor category). -/
noncomputable abbrev Definition_1_47_4 := @FiniteTensorCategoryFPData.regularObject
