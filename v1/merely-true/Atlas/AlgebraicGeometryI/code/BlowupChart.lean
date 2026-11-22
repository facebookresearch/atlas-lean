/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Degree.Lemmas

open Polynomial

/-- Ring map on `k[X][Y]` substituting `Y ↦ C(X) · Y`, modelling one affine chart of the
blow-up of the affine plane at the origin (where the exceptional `y`-coordinate is replaced
by the product of the base coordinate `X` and a new fibre coordinate `Y`). -/
noncomputable def blowupChartMap (k : Type*) [CommRing k] :
    Polynomial (Polynomial k) →+* Polynomial (Polynomial k) :=
  eval₂RingHom C (C X * X)

/-- The blow-up chart map computes as composition by `C X * X` in the `Y` variable. -/
lemma blowupChartMap_eq_comp (k : Type*) [CommRing k] (p : Polynomial (Polynomial k)) :
    blowupChartMap k p = p.comp (C X * X) := by
  simp [blowupChartMap, comp]

/-- Image of the outer variable `Y` (denoted `X` in `k[X][Y]`) under the blow-up chart map. -/
lemma blowupChartMap_X (k : Type*) [CommRing k] :
    blowupChartMap k X = C (X : Polynomial k) * X := by
  simp [blowupChartMap]

/-- The blow-up chart map fixes constants `C a` with `a ∈ k[X]`. -/
lemma blowupChartMap_C (k : Type*) [CommRing k] (a : Polynomial k) :
    blowupChartMap k (C a) = C a := by
  simp [blowupChartMap]

/-- The blow-up chart map is injective over a domain `k`; reflects that the affine chart is
birational to the affine plane. -/
theorem blowupChartMap_injective (k : Type*) [CommRing k] [IsDomain k] :
    Function.Injective (blowupChartMap k) := by
  intro p q hpq
  rw [← sub_eq_zero]
  have h : blowupChartMap k (p - q) = 0 := by rw [map_sub, sub_eq_zero, hpq]
  rw [blowupChartMap_eq_comp] at h
  rw [comp_eq_zero_iff] at h
  rcases h with h1 | ⟨_, hq⟩
  · exact h1
  · exfalso
    have h0 : (C (X : Polynomial k) * X : Polynomial (Polynomial k)).coeff 0 = 0 := by
      simp [coeff_mul]
    rw [h0, map_zero] at hq
    have : (C (X : Polynomial k) * X : Polynomial (Polynomial k)) ≠ 0 := by
      intro h0
      have := congr_arg (fun p => coeff p 1) h0
      simp at this
    exact this hq
