/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

noncomputable section

namespace LaurentSeries

open HahnSeries

variable (k : Type*) [Field k]

/-- The residue `k`-linear map on Laurent series: extracting the coefficient of `t^{-1}`,
the algebraic incarnation of the analytic residue at the origin. -/
def residue : LaurentSeries k →ₗ[k] k :=
  HahnSeries.coeff.linearMap (-1 : ℤ)

variable {k}

/-- Unfolding lemma: the residue of `f` is the coefficient of `t^{-1}`. -/
@[simp]
theorem residue_apply (f : LaurentSeries k) :
    residue k f = f.coeff (-1) := rfl

/-- The residue of `a · t^{-1}` is `a` (residue of a pure principal monomial). -/
@[simp]
theorem residue_single_neg_one (a : k) :
    residue k (HahnSeries.single (-1 : ℤ) a) = a :=
  HahnSeries.coeff_single_same (-1 : ℤ) a

/-- The residue of `a · t^n` for `n ≠ -1` is zero. -/
theorem residue_single_of_ne {n : ℤ} (h : n ≠ -1) (a : k) :
    residue k (HahnSeries.single n a) = 0 :=
  HahnSeries.coeff_single_of_ne (Ne.symm h)

/-- The residue map sends the zero Laurent series to zero. -/
@[simp]
theorem residue_zero : residue k (0 : LaurentSeries k) = 0 :=
  map_zero _

/-- Additivity of the residue map. -/
theorem residue_add (f g : LaurentSeries k) :
    residue k (f + g) = residue k f + residue k g :=
  map_add _ f g

/-- `k`-linearity (scalar compatibility) of the residue map. -/
theorem residue_smul (c : k) (f : LaurentSeries k) :
    residue k (c • f) = c • residue k f :=
  map_smul _ c f

/-- The residue of an honest power series (no principal part) is zero. -/
@[simp]
theorem residue_ofPowerSeries (f : PowerSeries k) :
    residue k (HahnSeries.ofPowerSeries ℤ k f) = 0 := by
  simp only [residue_apply, ofPowerSeries_apply]
  apply embDomain_notin_range
  simp only [Set.mem_range, not_exists]
  intro n
  show ¬ (↑n : ℤ) = (-1 : ℤ)
  omega

/-- Normalization: the residue of `1 · t^{-1}` is `1`, the canonical generator. -/
theorem residue_uniformizer_inv :
    residue k (HahnSeries.single (-1 : ℤ) (1 : k)) = 1 := by
  simp

end LaurentSeries
