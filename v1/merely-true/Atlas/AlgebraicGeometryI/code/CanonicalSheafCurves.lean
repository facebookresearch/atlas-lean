/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves
import Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective
import Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Atlas.AlgebraicGeometryI.code.RiemannRochCurves

set_option maxHeartbeats 800000

open RiemannRochCurves

noncomputable section

namespace CanonicalSheafCurves

/-- Existence witness for a smooth complete curve of genus `g`: a Dedekind `k`-algebra `A` whose
Kähler differential module has rank `g`. -/
def CurveWitness (g : ℤ) : Prop :=
  ∃ (k : Type) (_ : Field k) (A : Type) (_ : CommRing A) (_ : IsDomain A)
    (_ : IsDedekindDomain A) (_ : Algebra k A) (_ : Module.Finite k A),
    (Module.finrank k (Ω[A⁄k]) : ℤ) = g

/-- The rational numbers `ℚ` (as a `ℚ`-algebra) witness the genus-`0` case of `CurveWitness`. -/
theorem curveWitness_zero : CurveWitness 0 := by
  refine ⟨ℚ, inferInstance, ℚ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  simp only [Nat.cast_eq_zero]
  haveI := KaehlerDifferential.subsingleton_of_surjective ℚ ℚ (fun x => ⟨x, rfl⟩)
  exact Module.finrank_zero_of_subsingleton


/-- Numerical data of a smooth complete curve: genus `g`, canonical degree `degK`, Euler
characteristic homomorphism `χ : ℤ × ℤ →+ ℤ` (taking `(rank, degree)` to `χ(F)`), satisfying
the structure-sheaf and skyscraper normalisations plus existence of an underlying Dedekind
witness. -/
structure SmoothCompleteCurve where
  g : ℤ
  χ : ℤ × ℤ →+ ℤ
  degK : ℤ
  hg_nonneg : 0 ≤ g
  hχ_struct : χ (1, 0) = 1 - g
  hχ_sky : χ (0, 1) = 1
  hwf : CurveWitness g



/-- Class of the canonical sheaf of `C` in the Picard-style invariant `ℤ × ℤ` of
`(rank, degree)`: `K_C` is a line bundle (rank `1`) of degree `degK`. -/
def canonicalSheafClass (C : SmoothCompleteCurve) : ℤ × ℤ := (1, C.degK)

/-- Genus of the smooth complete curve `C`, as an integer. -/
def curveGenusOfSmooth (C : SmoothCompleteCurve) : ℤ := C.g

/-- Degree of the canonical divisor of `C`. -/
def canonicalDeg (C : SmoothCompleteCurve) : ℤ := C.degK

/-- Riemann-Roch on `C`: `χ(F) = d - r(g - 1)` for a sheaf of rank `r` and degree `d`. -/
theorem chi_eq_rr (C : SmoothCompleteCurve) (r d : ℤ) :
    C.χ (r, d) = d - r * (C.g - 1) :=
  riemann_roch_curves_thm C.g C.χ C.hχ_struct C.hχ_sky r d

/-- Specialisation of Riemann-Roch to the canonical class: `χ(K_C) = deg K_C + 1 - g`. -/
theorem chi_canonical_by_rr (C : SmoothCompleteCurve) :
    C.χ (1, C.degK) = C.degK + 1 - C.g := by
  rw [chi_eq_rr C 1 C.degK]; ring








/-- Numerical sanity check: `2·0 - 2 = -2`. -/
theorem deg_canonical_P1_check : 2 * (0 : ℤ) - 2 = -2 := by norm_num


/-- Numerical sanity check: `2·1 - 2 = 0`. -/
theorem deg_canonical_elliptic_check : 2 * (1 : ℤ) - 2 = 0 := by norm_num


/-- Numerical sanity check: `2·2 - 2 = 2`. -/
theorem deg_canonical_genus2_check : 2 * (2 : ℤ) - 2 = 2 := by norm_num


/-- Algebraic symmetry `(1 - g) + (g - 1) = 0` reflecting Serre duality on Euler characteristics. -/
theorem chi_symmetry (C : SmoothCompleteCurve) :
    (1 - C.g) + (C.g - 1) = 0 := by ring











/-- Adjunction identity for a plane curve of degree `d`: `d(d - 3) + 2 = (d - 1)(d - 2)`.
This encodes `2g - 2 = d(d - 3)` and `g = (d - 1)(d - 2)/2`. -/
theorem adjunction_genus_plane_curve (d : ℤ) :
    d * (d - 3) + 2 = (d - 1) * (d - 2) := by ring

/-- Canonical-degree form of the adjunction formula on a plane curve of degree `d`:
`2g - 2 = d(d - 3)`, where `g = (d - 1)(d - 2)/2`. -/
theorem adjunction_genus_plane_curve_degK (d : ℤ) (_hd : 0 ≤ d) :
    let g := (d - 1) * (d - 2) / 2
    2 * g - 2 = d * (d - 3) := by
  intro g
  have h_even : (2 : ℤ) ∣ (d - 1) * (d - 2) := by
    rcases Int.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨(d - 1) * (m - 1), by rw [hm]; ring⟩
    · exact ⟨m * (d - 2), by rw [hm]; ring⟩
  rw [show g = (d - 1) * (d - 2) / 2 from rfl, Int.mul_ediv_cancel' h_even]
  ring



end CanonicalSheafCurves

end
