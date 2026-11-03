/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannRochEulerCurves
import Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Atlas.AlgebraicGeometryI.code.RiemannFormRR

open CanonicalSheafCurves RiemannRochEulerCurves RiemannFormRR
open SheafCohCurvesFiniteness

noncomputable section

namespace RiemannRochRiemannForm

/-- Bundle of Serre-duality data for a sheaf on a smooth complete curve `C`
of class `(r, d)`: nonnegative integers `h0`, `h1` with `χ = h0 − h1` plus
an isomorphism `h1 = h0_dual` exhibiting Serre duality. -/
structure SerreDualityCurve (C : SmoothCompleteCurve) (r d : ℤ) where
  h0 : ℤ
  h1 : ℤ
  h0_dual : ℤ
  chi_decomp : C.χ (r, d) = h0 - h1
  serre_dual : h1 = h0_dual
  h0_nonneg : h0 ≥ 0
  h1_nonneg : h1 ≥ 0


/-- Cor 30 (Lec 24), Riemann form of Riemann–Roch: under Serre duality,
`h^0(ℰ) − h^0(K ⊗ ℰ*) = d + r(1 − g)`. -/
theorem riemann_form_general (C : SmoothCompleteCurve) (r d : ℤ)
    (SD : SerreDualityCurve C r d) :
    SD.h0 - SD.h0_dual = d + r * (1 - C.g) := by
  have hRR := chi_rr_curve C r d
  have hchi := SD.chi_decomp
  have hsd := SD.serre_dual
  linarith

/-- Subtractive reformulation of Cor 30: `h^0(ℰ) − h^0(K ⊗ ℰ*) = d − r(g − 1)`. -/
theorem riemann_form_general_alt (C : SmoothCompleteCurve) (r d : ℤ)
    (SD : SerreDualityCurve C r d) :
    SD.h0 - SD.h0_dual = d - r * (C.g - 1) := by
  have := riemann_form_general C r d SD
  linarith

/-- Cor 30 specialized to line bundles: `h^0(L) − h^0(K − L) = d + 1 − g`. -/
theorem riemann_form_line_bundle (C : SmoothCompleteCurve) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) :
    SD.h0 - SD.h0_dual = d + 1 - C.g := by
  have := riemann_form_general C 1 d SD
  linarith

/-- Riemann inequality for line bundles: `h^0(L) ≥ d + 1 − g`. -/
theorem riemann_inequality_line_bundle (C : SmoothCompleteCurve) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) :
    SD.h0 ≥ d + 1 - C.g := by
  have hform := riemann_form_line_bundle C d SD

  have h_dual_nn : SD.h0_dual ≥ 0 := by
    rw [← SD.serre_dual]
    exact SD.h1_nonneg
  linarith

/-- Riemann inequality in general rank: `h^0(ℰ) ≥ d + r(1 − g)`. -/
theorem riemann_inequality_general (C : SmoothCompleteCurve) (r d : ℤ)
    (SD : SerreDualityCurve C r d) :
    SD.h0 ≥ d + r * (1 - C.g) := by
  have hform := riemann_form_general C r d SD
  have h_dual_nn : SD.h0_dual ≥ 0 := by
    rw [← SD.serre_dual]
    exact SD.h1_nonneg
  linarith

/-- When `h^1` vanishes the Riemann inequality is an equality:
`h^0 = d + r(1 − g)`. -/
theorem riemann_roch_exact_when_h1_zero (C : SmoothCompleteCurve) (r d : ℤ)
    (SD : SerreDualityCurve C r d) (h1_zero : SD.h1 = 0) :
    SD.h0 = d + r * (1 - C.g) := by
  have hRR := chi_rr_curve C r d
  have := SD.chi_decomp
  linarith



/-- The Serre dual class of `(r, d)`: `(r, r·deg K − d)`. -/
def serreDualClass (C : SmoothCompleteCurve) (r d : ℤ) : ℤ × ℤ :=
  (r, r * C.degK - d)

/-- For a line bundle, the Serre dual class is `(1, deg K − d)`. -/
theorem serreDualClass_line_bundle (C : SmoothCompleteCurve) (d : ℤ) :
    serreDualClass C 1 d = (1, C.degK - d) := by
  simp [serreDualClass, one_mul]


/-- Smart constructor for `SerreDualityCurve` from raw data. -/
def mkSerreDualityCurve (C : SmoothCompleteCurve) (r d : ℤ)
    (h0 h1 : ℤ) (h0_dual : ℤ)
    (hchi : C.χ (r, d) = h0 - h1)
    (hsd : h1 = h0_dual)
    (hh0 : h0 ≥ 0) (hh1 : h1 ≥ 0) :
    SerreDualityCurve C r d :=
  { h0 := h0
    h1 := h1
    h0_dual := h0_dual
    chi_decomp := hchi
    serre_dual := hsd
    h0_nonneg := hh0
    h1_nonneg := hh1
    }

/-- Numerical avatar of Serre duality on `ℙ¹`:
`max(−n − 1, 0) = max((−2 − n) + 1, 0)`. -/
theorem serre_duality_P1_verify (n : ℤ) :
    (max (-n - 1) 0 : ℤ) = max ((-2 - n) + 1) 0 := by
  congr 1; ring

/-- Numerical Riemann–Roch on `ℙ¹`:
`max(n + 1, 0) − max(−n − 1, 0) = n + 1`. -/
theorem riemann_roch_P1_max_identity (n : ℤ) :
    (max (n + 1) 0 : ℤ) - max (-n - 1) 0 = n + 1 := by
  by_cases hn : 0 ≤ n
  ·
    have h1 : (n + 1 : ℤ) ≥ 0 := by linarith
    have h2 : (-n - 1 : ℤ) ≤ 0 := by linarith
    rw [max_eq_left h1, max_eq_right h2]
    simp
  ·
    push Not at hn
    have h1 : (n + 1 : ℤ) ≤ 0 := by linarith
    have h2 : (-n - 1 : ℤ) ≥ 0 := by linarith
    rw [max_eq_right h1, max_eq_left h2]
    linarith

/-- Riemann form of Riemann–Roch on `ℙ¹` rewritten with the `g = 0` rank
formula `n + 1 · (1 − 0)`. -/
theorem riemann_form_P1_verify (n : ℤ) :
    (max (n + 1) 0 : ℤ) - max (-n - 1) 0 = n + 1 * (1 - 0) :=
  riemann_roch_P1_max_identity n

/-- For `n ≥ 0`, Riemann inequality on `ℙ¹` is an equality:
`max(n + 1, 0) ≥ n + 1`. -/
theorem riemann_inequality_P1_nonneg (n : ℤ) (hn : n ≥ 0) :
    (max (n + 1) 0 : ℤ) ≥ n + 1 := by
  have : (n + 1 : ℤ) ≥ 0 := by linarith
  rw [max_eq_left this]






/-- Compatibility between the geometric Riemann–Roch on a smooth curve and
the algebraic Riemann–Roch on a Dedekind algebra: both yield
`l(D) − l(K − D) = deg D + 1 − g`. -/
theorem algebraic_abstract_consistency
    {k : Type*} [Field k] {A : Type*} [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A]
    (hrr : SatisfiesRiemannRoch k A) (I : Ideal A) (hI : I ≠ ⊥)
    (g : ℤ) (hg : g = (RiemannRochGeneral.arithmeticGenus k A : ℤ)) :
    (lD k A I : ℤ) - (lKD k A I : ℤ) =
      (RiemannRochGeneral.lineBundleDegree k A I : ℤ) + 1 - g := by
  have := hrr.rr_formula I hI
  rw [divisorEulerChar] at this
  linarith

/-- Cor 30 (Lec 24), combined form: Serre-duality equality and Riemann
inequality in arbitrary rank. -/
theorem corollary_30 (C : SmoothCompleteCurve) (r d : ℤ)
    (SD : SerreDualityCurve C r d) :
    SD.h0 - SD.h0_dual = d + r * (1 - C.g)
    ∧ SD.h0 ≥ d + r * (1 - C.g) := by
  exact ⟨riemann_form_general C r d SD, riemann_inequality_general C r d SD⟩

/-- Cor 30 for line bundles: Serre-duality equality and Riemann inequality. -/
theorem corollary_30_line_bundle (C : SmoothCompleteCurve) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) :
    SD.h0 - SD.h0_dual = d + 1 - C.g
    ∧ SD.h0 ≥ d + 1 - C.g :=
  ⟨riemann_form_line_bundle C d SD, riemann_inequality_line_bundle C d SD⟩

/-- Dimensional avatar of Serre duality on `ℙ¹`. -/
theorem serre_duality_P1_dims (n : ℤ) :
    (max (-n - 1) 0 : ℤ) = max ((-2 - n) + 1) 0 := by
  congr 1; ring

/-- Vanishing of dual cohomology on `ℙ¹` for `n ≥ 0`. -/
theorem serre_duality_P1_vanishing (n : ℤ) (hn : n ≥ 0) :
    max (-n - 1) 0 = (0 : ℤ) ∧ max ((-2 - n) + 1) 0 = (0 : ℤ) := by
  constructor
  · have : -n - 1 ≤ 0 := by linarith
    exact max_eq_right this
  · have : (-2 - n) + 1 ≤ 0 := by linarith
    exact max_eq_right this

/-- Strict non-vanishing of `H^1` on `ℙ¹` for `n < −1`. -/
theorem serre_duality_P1_nonvanishing (n : ℤ) (hn : n < -1) :
    max (-n - 1) 0 > (0 : ℤ) := by
  have : -n - 1 > 0 := by linarith
  rw [max_eq_left (by linarith : (0 : ℤ) ≤ -n - 1)]
  linarith

end RiemannRochRiemannForm

end
