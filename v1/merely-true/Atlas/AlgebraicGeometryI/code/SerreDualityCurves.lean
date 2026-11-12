/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves
import Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Atlas.AlgebraicGeometryI.code.SerreDualityLinear
import Atlas.AlgebraicGeometryI.code.SerreDualityGeneral
import Atlas.AlgebraicGeometryI.code.ResidueSum
import Atlas.AlgebraicGeometryI.code.DedekindCurve

noncomputable section

namespace SerreDualityCurves

open CanonicalSheafCurves RiemannRochCurves SerreDualityP1
open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology


section ResidueMap

variable (k : Type*) [Field k]

/-- The residue map `(ℤ →₀ k) →ₗ[k] k` sending a Laurent polynomial to its
coefficient at index `-1`. -/
def residueMap : (ℤ →₀ k) →ₗ[k] k where
  toFun f := f (-1)
  map_add' f g := Finsupp.add_apply f g (-1)
  map_smul' c f := Finsupp.smul_apply c f (-1)

/-- Unfolds `residueMap` to the coefficient at index `-1`. -/
@[simp]
theorem residueMap_apply (f : ℤ →₀ k) : residueMap k f = f (-1) := rfl

/-- The residue of a single-term Laurent polynomial concentrated at index `-1` is its coefficient. -/
theorem residueMap_single_neg_one (a : k) :
    residueMap k (Finsupp.single (-1 : ℤ) a) = a :=
  Finsupp.single_eq_same

/-- Single-term Laurent polynomials concentrated at any index other than `-1`
have residue zero. -/
theorem residueMap_single_ne (n : ℤ) (hn : n ≠ -1) (a : k) :
    residueMap k (Finsupp.single n a) = 0 :=
  Finsupp.single_eq_of_ne (Ne.symm hn)

end ResidueMap


section ExactForms

variable (k : Type*) [Field k]

/-- Coefficient of the formal derivative: `(d/dz f)(m) = (m+1) · f(m+1)`. -/
def derivCoeff (f : ℤ →₀ k) (m : ℤ) : k :=
  (↑(m + 1) : k) * f (m + 1)

/-- The `(-1)`-coefficient of a formal derivative vanishes (the prefactor `0 · f(0)` is zero). -/
theorem derivCoeff_neg_one (f : ℤ →₀ k) :
    derivCoeff k f (-1) = 0 := by
  simp [derivCoeff]

/-- The residue of an exact differential `d(a · z^n) = n · a · z^{n-1}` vanishes. -/
theorem residue_of_exact_zero (n : ℤ) (a : k) :
    residueMap k (Finsupp.single (n - 1) ((↑n : k) * a)) = 0 := by
  by_cases h : n - 1 = -1
  ·
    have hn : n = 0 := by omega
    subst hn; simp
  ·
    exact residueMap_single_ne k (n - 1) h ((↑n : k) * a)

/-- The residue annihilates exact forms: formal derivatives have vanishing `-1`-coefficient. -/
theorem residue_annihilates_derivs (f : ℤ →₀ k) :
    derivCoeff k f (-1) = 0 :=
  derivCoeff_neg_one k f

end ExactForms


section ResiduePairing

variable (k : Type*) [Field k]

/-- The residue pairing `⟨f, g⟩ = ∑ i f(i) · g(-1 - i)`, which extracts
the `-1`-coefficient of the convolution product. -/
def residuePairing (f g : ℤ →₀ k) : k :=
  ∑ i ∈ f.support, f i * g (-1 - i)

/-- The residue pairing on single-term Laurent polynomials: equals `a · b`
when `i + j = -1` and `0` otherwise. -/
theorem residuePairing_single (i j : ℤ) (a b : k) :
    residuePairing k (Finsupp.single i a) (Finsupp.single j b) =
    if i + j = -1 then a * b else 0 := by
  unfold residuePairing
  by_cases ha : a = 0
  · simp [ha, Finsupp.single_zero, Finsupp.support_zero]
  · rw [Finsupp.support_single_ne_zero _ ha, Finset.sum_singleton, Finsupp.single_eq_same]
    by_cases hij : i + j = -1
    · have hj : j = -1 - i := by omega
      simp only [hij, ↓reduceIte]
      rw [hj, show (Finsupp.single (-1 - i) b : ℤ →₀ k) (-1 - i) = b from
        Finsupp.single_eq_same]
    · simp only [hij, ↓reduceIte]
      have hne : (-1 - i : ℤ) ≠ j := by omega
      rw [show (Finsupp.single j b : ℤ →₀ k) (-1 - i) = 0 from
        Finsupp.single_eq_of_ne hne]
      ring

/-- Symmetry of the residue pairing on single-term Laurent polynomials. -/
theorem residuePairing_single_comm (i j : ℤ) (a b : k) :
    residuePairing k (Finsupp.single i a) (Finsupp.single j b) =
    residuePairing k (Finsupp.single j b) (Finsupp.single i a) := by
  rw [residuePairing_single, residuePairing_single]
  by_cases h : i + j = -1
  · have : j + i = -1 := by linarith
    simp [h, this, mul_comm]
  · have : j + i ≠ -1 := by omega
    simp [h, this]

end ResiduePairing


section GeneralCurves





end GeneralCurves


section LocallyFreeSheaf

/-- Numerical model of a locally free sheaf on a curve `C`: tracks rank and degree. -/
@[ext]
structure LocallyFreeSheaf (C : SmoothCompleteCurve) where
  rk : ℕ
  deg : ℤ


/-- The K-theory class of a locally free sheaf is the pair `(rank, degree) ∈ ℤ × ℤ`. -/
def LocallyFreeSheaf.K0class {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) : ℤ × ℤ := (↑E.rk, E.deg)

/-- The Euler characteristic `χ(E) = h⁰(E) - h¹(E)` of a locally free sheaf,
computed from its rank and degree via Riemann–Roch. -/
def LocallyFreeSheaf.chi {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) : ℤ := C.χ E.K0class

/-- The Serre dual `E∨ ⊗ K` at the level of `(rank, degree)`: same rank,
degree replaced by `rank · deg K − deg E`. -/
def LocallyFreeSheaf.serreDual {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) : LocallyFreeSheaf C where
  rk := E.rk
  deg := ↑E.rk * C.degK - E.deg

/-- Unfolds the degree of the Serre dual. -/
theorem LocallyFreeSheaf.serreDual_deg {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) :
    E.serreDual.deg = ↑E.rk * C.degK - E.deg := rfl


/-- Serre duality is an involution at the numerical level: `(E∨ ⊗ K)∨ ⊗ K = E`. -/
theorem LocallyFreeSheaf.serreDual_serreDual {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) :
    E.serreDual.serreDual = E := by
  ext <;> simp [serreDual]

/-- The line bundle of a given degree. -/
def LocallyFreeSheaf.ofIdeal (C : SmoothCompleteCurve) (deg : ℤ) :
    LocallyFreeSheaf C where
  rk := 1
  deg := deg

/-- The structure sheaf `O_C` as a locally free sheaf of rank `1` and degree `0`. -/
def LocallyFreeSheaf.structureSheaf (C : SmoothCompleteCurve) :
    LocallyFreeSheaf C where
  rk := 1
  deg := 0

/-- The canonical bundle `K_C` as a locally free sheaf of rank `1` and degree `deg K`. -/
def LocallyFreeSheaf.canonical (C : SmoothCompleteCurve) :
    LocallyFreeSheaf C where
  rk := 1
  deg := C.degK

/-- Standalone alias for the structure sheaf of `C`. -/
def structureSheaf (C : SmoothCompleteCurve) : LocallyFreeSheaf C where
  rk := 1
  deg := 0

/-- Standalone alias for the canonical sheaf of `C`. -/
def canonicalSheaf (C : SmoothCompleteCurve) : LocallyFreeSheaf C where
  rk := 1
  deg := C.degK

/-- The Serre dual of `O_C` is `K_C` numerically. -/
theorem structureSheaf_serreDual (C : SmoothCompleteCurve) :
    (structureSheaf C).serreDual = canonicalSheaf C := by
  ext <;> simp [structureSheaf, canonicalSheaf, LocallyFreeSheaf.serreDual]


end LocallyFreeSheaf


section P1Verification

open RiemannRoch in
/-- Serre duality on `ℙ¹` at the level of dimensions: `dim H¹(O(n)) = dim H⁰(O(-2 - n))`. -/
theorem serre_duality_P1_dimension (k : Type) [Field k] (n : ℤ) :
    RiemannRoch.dimH1 k n = RiemannRoch.dimH0 k (-2 - n) :=
  RiemannRoch.serre_duality_P1 k n








variable (k : Type) [Field k]

/-- Serre duality on `ℙ¹` (nonempty version): for `n < -1`, the quotient
`(ℤ →₀ k) / (NonNeg ⊔ AtMost n)` is linearly equivalent to `CechH⁰(-2 - n)`. -/
theorem serre_duality_P1_via_shift (n : ℤ) (hn : n < -1) :
    Nonempty (((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) ≃ₗ[k]
      ↥(CechH0 k (-2 - n))) :=
  ⟨SerreDualityP1.serre_duality_P1 k n hn⟩

/-- Serre duality on `ℙ¹` at the dimension level: for `n < -1`,
`dim H¹(O(n)) = dim H⁰(O(-2 - n))`. -/
theorem serre_duality_P1_finrank_eq (n : ℤ) (hn : n < -1) :
    Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) =
    Module.finrank k ↥(CechH0 k (-2 - n)) :=
  SerreDualityP1.serre_duality_finrank k n hn

end P1Verification


section ResidueConnection

variable (k : Type*) [Field k]

/-- The residue pairing of `a · z^i` with `g` equals `a · g(-1 - i)`. -/
theorem residuePairing_via_shift (i : ℤ) (a : k) (g : ℤ →₀ k) :
    residuePairing k (Finsupp.single i a) g = a * g (residueShift i) := by
  unfold residuePairing residueShift
  by_cases ha : a = 0
  · simp [ha, Finsupp.single_zero, Finsupp.support_zero]
  · rw [Finsupp.support_single_ne_zero _ ha, Finset.sum_singleton, Finsupp.single_eq_same]

/-- The shift `i ↦ -1 - i` sends `[0, n]` bijectively onto `[-1 - n, -1]`,
showing the pairing matches degrees of one side with degrees of the dual side. -/
theorem residue_shift_is_pairing_bijection (n : ℤ) :
    residueShift '' (Set.Icc 0 n) = Set.Icc (-1 - n) (-1) := by
  ext x
  simp only [Set.mem_image, Set.mem_Icc, residueShift]
  constructor
  · rintro ⟨y, ⟨hy0, hyn⟩, rfl⟩; constructor <;> omega
  · intro ⟨hx_lb, hx_ub⟩
    exact ⟨-1 - x, ⟨by omega, by omega⟩, by omega⟩

end ResidueConnection


section TheoremStatement




end TheoremStatement


section Applications

/-- Riemann–Roch in Serre form: `h⁰(D) − h⁰(K − D) = d + 1 − g`. -/
theorem riemann_roch_serre_form_general (C : SmoothCompleteCurve) (d : ℤ)
    (h0_D h0_KD : ℤ)
    (hRR : h0_D - h0_KD = C.χ (1, d))
    : h0_D - h0_KD = d + 1 - C.g := by
  rw [chi_eq_rr C 1 d] at hRR; linarith

/-- Riemann's inequality: `h⁰(D) ≥ d + 1 − g`, derived from Riemann–Roch
and the non-negativity of `h¹`. -/
theorem riemann_inequality_from_RR (C : SmoothCompleteCurve) (d h0 h1 : ℤ)
    (hh1_nn : h1 ≥ 0)
    (hRR : h0 - h1 = d + 1 - C.g) :
    h0 ≥ d + 1 - C.g := by linarith


end Applications


section DedekindBridge




end DedekindBridge

end SerreDualityCurves

end
