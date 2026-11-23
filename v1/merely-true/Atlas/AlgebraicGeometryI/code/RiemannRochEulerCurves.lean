/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves

open RiemannRochCurves CanonicalSheafCurves

noncomputable section

namespace RiemannRochEulerCurves

/-- Riemann–Roch in additive form for a curve: `χ(r, d) = d + r(1 - g)`. -/
theorem chi_rr_curve (C : SmoothCompleteCurve) (r d : ℤ) :
    C.χ (r, d) = d + r * (1 - C.g) := by
  have := chi_eq_rr C r d
  linarith

/-- Riemann–Roch in subtractive form: `χ(r, d) = d - r(g - 1)`. -/
theorem chi_rr_curve_alt (C : SmoothCompleteCurve) (r d : ℤ) :
    C.χ (r, d) = d - r * (C.g - 1) :=
  chi_eq_rr C r d

/-- Additivity of the Euler-characteristic hom on the Grothendieck-class
group: `χ(a + b) = χ(a) + χ(b)`. -/
theorem euler_char_additive (C : SmoothCompleteCurve) (a b : ℤ × ℤ) :
    C.χ (a + b) = C.χ a + C.χ b :=
  map_add C.χ a b

/-- Negation under the Euler characteristic: `χ(-a) = -χ(a)`. -/
theorem euler_char_neg (C : SmoothCompleteCurve) (a : ℤ × ℤ) :
    C.χ (-a) = -(C.χ a) :=
  map_neg C.χ a

/-- Integer scaling under the Euler characteristic: `χ(n • a) = n • χ(a)`. -/
theorem euler_char_zsmul (C : SmoothCompleteCurve) (n : ℤ) (a : ℤ × ℤ) :
    C.χ (n • a) = n • (C.χ a) :=
  map_zsmul C.χ n a

/-- `χ(0) = 0`. -/
theorem euler_char_zero (C : SmoothCompleteCurve) :
    C.χ 0 = 0 :=
  map_zero C.χ

/-- Any additive map agreeing with `χ` on the structure sheaf and a
skyscraper equals `χ` on all classes. -/
theorem euler_char_determines_chi (C : SmoothCompleteCurve) (f : ℤ × ℤ →+ ℤ)
    (hf_struct : f (1, 0) = 1 - C.g) (hf_sky : f (0, 1) = 1) :
    ∀ p : ℤ × ℤ, f p = C.χ p := by
  intro ⟨r, d⟩
  have hf := riemann_roch_curves_thm C.g f hf_struct hf_sky r d
  rw [hf, ← chi_eq_rr C r d]

/-- The Euler characteristic of the structure sheaf is `1 - g`. -/
theorem chi_structure_sheaf_curve (C : SmoothCompleteCurve) :
    C.χ (1, 0) = 1 - C.g :=
  C.hχ_struct

/-- The Euler characteristic of a length-1 skyscraper is `1`. -/
theorem euler_char_skyscraper (C : SmoothCompleteCurve) :
    C.χ (0, 1) = 1 :=
  C.hχ_sky

/-- Riemann–Roch for line bundles: `χ(L_d) = d + 1 - g`. -/
theorem euler_char_line_bundle (C : SmoothCompleteCurve) (d : ℤ) :
    C.χ (1, d) = d + 1 - C.g := by
  have := chi_rr_curve C 1 d; linarith

/-- Euler characteristic of a torsion sheaf of length `d`: `χ(0, d) = d`. -/
theorem euler_char_torsion (C : SmoothCompleteCurve) (d : ℤ) :
    C.χ (0, d) = d := by
  have := chi_rr_curve C 0 d; linarith

/-- Euler characteristic of a free sheaf of rank `r`: `χ(r, 0) = r(1 - g)`. -/
theorem euler_char_free (C : SmoothCompleteCurve) (r : ℤ) :
    C.χ (r, 0) = r * (1 - C.g) := by
  have := chi_rr_curve C r 0; linarith

/-- Twisting by a point shifts the Euler characteristic by the rank. -/
theorem euler_char_twist (C : SmoothCompleteCurve) (r d n : ℤ) :
    C.χ (r, d + n * r) = C.χ (r, d) + n * r := by
  rw [chi_rr_curve C r (d + n * r), chi_rr_curve C r d]
  ring



/-- Riemann inequality: from `χ(L) = h^0 - h^1 ≥ h^0 - (h^0 - (d + 1 - g)) - ...`
combined with `h^1 ≥ 0` we get `h^0 ≥ d + 1 - g`. -/
theorem h0_lower_bound (C : SmoothCompleteCurve) (d h0 h1 : ℤ)
    (hchi : C.χ (1, d) = h0 - h1) (hh1 : h1 ≥ 0) :
    h0 ≥ d + 1 - C.g := by
  have hRR := euler_char_line_bundle C d
  linarith

/-- When `h^1 = 0`, Riemann–Roch is exact: `h^0 = d + 1 - g`. -/
theorem h0_of_vanishing_h1 (C : SmoothCompleteCurve) (d h0 : ℤ)
    (hchi : C.χ (1, d) = h0) :
    h0 = d + 1 - C.g := by
  have := euler_char_line_bundle C d
  linarith

/-- For positive rank and large enough degree, the Euler characteristic is
strictly positive. -/
theorem euler_char_positive_slope (C : SmoothCompleteCurve) (r d : ℤ)
    (_hr : r > 0) (hd : d > r * (C.g - 1)) :
    C.χ (r, d) > 0 := by
  rw [chi_rr_curve_alt C r d]
  linarith



/-- Riemann–Roch on `ℙ¹` (`g = 0`): `χ(𝒪(d)) = d + 1`. -/
theorem euler_char_P1 (C : SmoothCompleteCurve) (hg : C.g = 0) (d : ℤ) :
    C.χ (1, d) = d + 1 := by
  rw [euler_char_line_bundle]; linarith

/-- Riemann–Roch on an elliptic curve (`g = 1`): `χ(𝒪(d)) = d`. -/
theorem euler_char_elliptic (C : SmoothCompleteCurve) (hg : C.g = 1) (d : ℤ) :
    C.χ (1, d) = d := by
  rw [euler_char_line_bundle]; linarith

/-- For a genus-2 curve, `χ(𝒪) = -1`. -/
theorem euler_char_genus2_O (C : SmoothCompleteCurve) (hg : C.g = 2) :
    C.χ (1, 0) = -1 := by
  rw [chi_structure_sheaf_curve]; linarith


/-- Increasing the degree by 1 shifts `χ` by 1: `χ(r, d + 1) = χ(r, d) + 1`. -/
theorem euler_char_degree_shift (C : SmoothCompleteCurve) (r d : ℤ) :
    C.χ (r, d + 1) = C.χ (r, d) + 1 := by
  rw [chi_rr_curve C r (d + 1), chi_rr_curve C r d]
  ring

/-- Increasing the rank by 1 shifts `χ` by `1 - g`. -/
theorem euler_char_rank_shift (C : SmoothCompleteCurve) (r d : ℤ) :
    C.χ (r + 1, d) = C.χ (r, d) + (1 - C.g) := by
  rw [chi_rr_curve C (r + 1) d, chi_rr_curve C r d]
  ring

/-- The Euler characteristic difference along the degree axis equals the
degree: `χ(r, d) - χ(r, 0) = d`. -/
theorem euler_char_minus_trivial (C : SmoothCompleteCurve) (r d : ℤ) :
    C.χ (r, d) - C.χ (r, 0) = d := by
  rw [chi_rr_curve C r d, chi_rr_curve C r 0]
  ring

end RiemannRochEulerCurves

end
