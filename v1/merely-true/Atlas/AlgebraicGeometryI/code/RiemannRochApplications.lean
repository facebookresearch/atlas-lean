/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannRochEulerCurves
import Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Atlas.AlgebraicGeometryI.code.RiemannRochRiemannForm
import Atlas.AlgebraicGeometryI.code.DedekindCurve

open CanonicalSheafCurves RiemannRochEulerCurves RiemannRochRiemannForm
open SheafCohCurvesFiniteness

noncomputable section

namespace RiemannRochApplications



/-- Serre duality for the structure sheaf: `h^0(𝒪_C) = 1` and `h^1(𝒪_C) = h^0(ω_C) = g`. -/
theorem corollary_29_serre_duality (C : SmoothCompleteCurve) (_hg : C.g ≥ 0)
    (h0_O h1_O h0_K : ℤ)
    (_hchi_O : C.χ (1, 0) = h0_O - h1_O)
    (hSD_O : h1_O = h0_K)
    (_hh0_O : h0_O = 1) (hh1_O : h1_O = C.g) :
    h0_K = C.g := by
  linarith







/-- In the high-degree case where `h^1 = 0`, Riemann–Roch is exact:
`h^0(L) = d + 1 - g`. -/
theorem high_degree_exact_rr (C : SmoothCompleteCurve) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 = d + 1 - C.g := by
  have := riemann_roch_exact_when_h1_zero C 1 d SD h1_zero
  linarith

/-- For `d ≥ 2g - 1` (and `h^1 = 0`), `h^0(L) ≥ g`. -/
theorem high_degree_has_sections (C : SmoothCompleteCurve) (d : ℤ)
    (hd : d ≥ 2 * C.g - 1) (_hg : C.g ≥ 0)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 ≥ C.g := by
  have := high_degree_exact_rr C d SD h1_zero
  linarith

/-- For `d ≥ 2g`, `h^0(L) ≥ g + 1`. -/
theorem very_high_degree_sections (C : SmoothCompleteCurve) (d : ℤ)
    (hd : d ≥ 2 * C.g)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 ≥ C.g + 1 := by
  have := high_degree_exact_rr C d SD h1_zero
  linarith

/-- For a genus-0 curve (i.e., `ℙ¹`), `χ(𝒪) = 1`. -/
theorem genus_zero_chi_O (C : SmoothCompleteCurve) (hg : C.g = 0) :
    C.χ (1, 0) = 1 := by
  rw [chi_structure_sheaf_curve]; linarith


/-- For a genus-0 curve, the Euler characteristic of `𝒪(1)` is 2. -/
theorem genus_zero_point_chi (C : SmoothCompleteCurve) (hg : C.g = 0) :
    C.χ (1, 1) = 2 := by
  rw [euler_char_line_bundle]; linarith

/-- On a genus-0 curve, `h^0(𝒪(1)) = 2` (the two sections defining the
projective embedding). -/
theorem genus_zero_point_sections (C : SmoothCompleteCurve) (hg : C.g = 0)
    (SD : SerreDualityCurve C 1 1) (h1_zero : SD.h1 = 0) :
    SD.h0 = 2 := by
  have := riemann_roch_exact_when_h1_zero C 1 1 SD h1_zero
  linarith [hg]


/-- For a genus-0 curve and any `d`, when `h^1 = 0`, `h^0(L(d)) = d + 1`. -/
theorem genus_zero_sections (C : SmoothCompleteCurve) (hg : C.g = 0) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 = d + 1 := by
  have := riemann_roch_exact_when_h1_zero C 1 d SD h1_zero
  linarith [hg]

/-- For an elliptic curve (genus 1), `χ(𝒪) = 0`. -/
theorem elliptic_chi_O (C : SmoothCompleteCurve) (hg : C.g = 1) :
    C.χ (1, 0) = 0 := by
  rw [chi_structure_sheaf_curve]; linarith


/-- For an elliptic curve, the Euler characteristic of a line bundle of
degree `d` is `d`. -/
theorem elliptic_chi (C : SmoothCompleteCurve) (hg : C.g = 1) (d : ℤ) :
    C.χ (1, d) = d := by
  rw [euler_char_line_bundle]; linarith

/-- For an elliptic curve with `h^1 = 0`, `h^0(L) = d`. -/
theorem elliptic_sections (C : SmoothCompleteCurve) (hg : C.g = 1) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 = d := by
  have := riemann_roch_exact_when_h1_zero C 1 d SD h1_zero
  linarith [hg]

/-- An elliptic curve embeds as a smooth cubic in `ℙ²` via a degree-3 line
bundle: `h^0(𝒪(3)) = 3`. -/
theorem elliptic_cubic_embedding (C : SmoothCompleteCurve) (hg : C.g = 1)
    (SD : SerreDualityCurve C 1 3) (h1_zero : SD.h1 = 0) :
    SD.h0 = 3 :=
  elliptic_sections C hg 3 SD h1_zero



/-- For a genus-2 curve and high degree (so `h^1 = 0`), `h^0(L) = d - 1`. -/
theorem genus2_high_degree (C : SmoothCompleteCurve) (hg : C.g = 2) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 = d - 1 := by
  have := riemann_roch_exact_when_h1_zero C 1 d SD h1_zero
  linarith [hg]

/-- Verification: on `ℙ¹`, `dim H^0(𝒪) = 1`. -/
theorem P1_verify_H0_structure (k : Type) [Field k] :
    Module.finrank k (SheafCohomology.H0 k 0) = 1 := by
  exact SheafCohomology.finrank_H0_of_nonneg k 0 le_rfl

/-- Verification: on `ℙ¹`, `dim H^1(𝒪) = 0`. -/
theorem P1_verify_H1_structure (k : Type) [Field k] :
    Module.finrank k (SheafCohomology.H1 k 0) = 0 := by
  exact SheafCohomology.finrank_H1_of_nonneg k 0 le_rfl

/-- Verification: on `ℙ¹`, `χ(𝒪) = 1`. -/
theorem P1_verify_euler_char_O (k : Type) [Field k] :
    (Module.finrank k (SheafCohomology.H0 k 0) : ℤ) -
    (Module.finrank k (SheafCohomology.H1 k 0) : ℤ) = 1 := by
  rw [P1_verify_H0_structure, P1_verify_H1_structure]
  norm_num

/-- Serre duality on `ℙ¹`: `dim H^1(𝒪(n)) = dim H^0(𝒪(-2 - n))`. -/
theorem P1_verify_serre_duality (k : Type) [Field k] (n : ℤ) :
    Module.finrank k (SheafCohomology.H1 k n) =
    Module.finrank k (SheafCohomology.H0 k (-2 - n)) := by
  by_cases hn : 0 ≤ n
  · exact SheafCohomology.serre_duality_nonneg k n hn
  · exact SheafCohomology.serre_duality_neg k n (not_le.mp hn)

/-- On `ℙ¹`, `dim H^0(𝒪(1)) = 2`. -/
theorem P1_verify_H0_degree1 (k : Type) [Field k] :
    Module.finrank k (SheafCohomology.H0 k 1) = 2 := by
  rw [SheafCohomology.finrank_H0_of_nonneg k 1 (by norm_num)]
  simp

/-- On `ℙ¹`, `dim H^1(𝒪(1)) = 0`. -/
theorem P1_verify_H1_degree1 (k : Type) [Field k] :
    Module.finrank k (SheafCohomology.H1 k 1) = 0 := by
  exact SheafCohomology.finrank_H1_of_nonneg k 1 (by norm_num)

/-- On `ℙ¹`, for `n ≥ 0`, `dim H^0(𝒪(n)) = n + 1`. -/
theorem P1_verify_H0_nonneg (k : Type) [Field k] (n : ℤ) (hn : 0 ≤ n) :
    (Module.finrank k (SheafCohomology.H0 k n) : ℤ) = n + 1 := by
  rw [SheafCohomology.finrank_H0_of_nonneg k n hn]
  omega

/-- On `ℙ¹`, for `n ≥ 0`, `dim H^1(𝒪(n)) = 0`. -/
theorem P1_verify_H1_nonneg (k : Type) [Field k] (n : ℤ) (hn : 0 ≤ n) :
    Module.finrank k (SheafCohomology.H1 k n) = 0 := by
  exact SheafCohomology.finrank_H1_of_nonneg k n hn

/-- On `ℙ¹`, `dim H^0(𝒪(-1)) = 0`. -/
theorem P1_verify_H0_neg1 (k : Type) [Field k] :
    Module.finrank k (SheafCohomology.H0 k (-1)) = 0 := by
  exact SheafCohomology.finrank_H0_of_neg k (-1) (by norm_num)

/-- On `ℙ¹`, `dim H^1(𝒪(-2)) = 1` (corresponding to the canonical bundle). -/
theorem P1_verify_H1_neg2 (k : Type) [Field k] :
    Module.finrank k (SheafCohomology.H1 k (-2)) = 1 := by
  rw [SheafCohomology.finrank_H1_of_neg k (-2) (by norm_num)]
  norm_num



/-- The genus can be recovered from the structure sheaf's Euler characteristic:
`g = 1 - χ(𝒪)`. -/
theorem genus_from_euler_char (C : SmoothCompleteCurve) :
    C.g = 1 - C.χ (1, 0) := by
  rw [chi_structure_sheaf_curve]; ring


/-- The Riemann inequality from the Serre duality data: `d + 1 - g ≤ h^0(L)`. -/
theorem riemann_inequality_from_SD (C : SmoothCompleteCurve) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) :
    d + 1 - C.g ≤ SD.h0 := by
  exact riemann_inequality_line_bundle C d SD


/-- For the self-dual class `L = K^{1/2}` (degree `g - 1`), the Euler
characteristic is zero. -/
theorem self_dual_chi_zero (C : SmoothCompleteCurve) :
    C.χ (1, C.g - 1) = 0 := by
  rw [euler_char_line_bundle]; ring



end RiemannRochApplications

end
