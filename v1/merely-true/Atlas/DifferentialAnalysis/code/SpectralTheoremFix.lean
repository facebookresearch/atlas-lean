/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Positive
import Atlas.DifferentialAnalysis.code.HilbertSpace

noncomputable section

open scoped ComplexInnerProductSpace

namespace SpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The infimum of the Rayleigh quotient of a continuous linear operator `T` over nonzero
vectors. For self-adjoint `T`, this is the lower endpoint of `spectrum ℝ T`. -/
def rayleighInf (T : H →L[ℂ] H) : ℝ :=
  ⨅ x : { x : H // x ≠ 0 }, T.rayleighQuotient x

/-- The supremum of the Rayleigh quotient of a continuous linear operator `T` over nonzero
vectors. For self-adjoint `T`, this is the upper endpoint of `spectrum ℝ T`. -/
def rayleighSup (T : H →L[ℂ] H) : ℝ :=
  ⨆ x : { x : H // x ≠ 0 }, T.rayleighQuotient x

set_option maxHeartbeats 2000000 in
/-- For a self-adjoint operator `T`, `⟨(t·I − T)x, x⟩` equals the real number
`t‖x‖² − ⟨Tx,x⟩_ℝ` cast into `ℂ`. -/
lemma inner_shifted_eq (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (t : ℝ) (x : H) :
    @inner ℂ H _ ((algebraMap ℝ (H →L[ℂ] H) t - T) x) x =
    ((t * ‖x‖ ^ 2 - T.reApplyInnerSelf x : ℝ) : ℂ) := by
  have halg : algebraMap ℝ (H →L[ℂ] H) t = (t : ℂ) • (1 : H →L[ℂ] H) := by
    simp [Algebra.algebraMap_eq_smul_one]
  simp only [halg, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, inner_sub_left, inner_smul_left,
    Complex.conj_ofReal, inner_self_eq_norm_sq_to_K,
    ← hT.isSymmetric.coe_reApplyInnerSelf_apply (x := x),
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow]
  rfl

omit [CompleteSpace H] in
/-- The Rayleigh quotient is bounded above by `‖T‖`, so its range over nonzero vectors
admits a supremum. -/
lemma bddAbove_rayleigh (T : H →L[ℂ] H) :
    BddAbove (Set.range fun (x : { x : H // x ≠ 0 }) => T.rayleighQuotient x.val) :=
  ⟨‖T‖, fun _ ⟨y, h⟩ => h ▸ le_of_abs_le (T.rayleighQuotient_le_norm y.val)⟩

omit [CompleteSpace H] in
/-- The Rayleigh quotient is bounded below by `−‖T‖`, so its range over nonzero vectors
admits an infimum. -/
lemma bddBelow_rayleigh (T : H →L[ℂ] H) :
    BddBelow (Set.range fun (x : { x : H // x ≠ 0 }) => T.rayleighQuotient x.val) :=
  ⟨-‖T‖, fun _ ⟨y, h⟩ => h ▸ neg_le_of_abs_le (T.rayleighQuotient_le_norm y.val)⟩

omit [CompleteSpace H] in
/-- Pointwise bound: `Re⟨Tx, x⟩ ≤ rayleighSup T · ‖x‖²`. -/
lemma reApplyInnerSelf_le_rayleighSup_mul (T : H →L[ℂ] H) (x : H) :
    T.reApplyInnerSelf x ≤ rayleighSup T * ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · simp [hx, ContinuousLinearMap.reApplyInnerSelf_apply]
  · have h := le_ciSup (bddAbove_rayleigh T) ⟨x, hx⟩
    change T.rayleighQuotient x ≤ rayleighSup T at h
    rwa [ContinuousLinearMap.rayleighQuotient, div_le_iff₀ (by positivity : 0 < ‖x‖ ^ 2)] at h

omit [CompleteSpace H] in
/-- Pointwise bound: `rayleighInf T · ‖x‖² ≤ Re⟨Tx, x⟩`. -/
lemma rayleighInf_mul_le_reApplyInnerSelf (T : H →L[ℂ] H) (x : H) :
    rayleighInf T * ‖x‖ ^ 2 ≤ T.reApplyInnerSelf x := by
  by_cases hx : x = 0
  · simp [hx, ContinuousLinearMap.reApplyInnerSelf_apply]
  · have h := ciInf_le (bddBelow_rayleigh T) ⟨x, hx⟩
    change rayleighInf T ≤ T.rayleighQuotient x at h
    rwa [ContinuousLinearMap.rayleighQuotient, le_div_iff₀ (by positivity : 0 < ‖x‖ ^ 2)] at h


set_option maxHeartbeats 4000000 in
/-- Spectral inclusion for self-adjoint operators: `spectrum ℝ T ⊆ [rayleighInf T, rayleighSup T]`.
This is one direction of the Rayleigh quotient characterization of the spectrum
(Melrose Prop 16.2). -/
theorem selfAdjoint_spectrum_subset_Icc
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    spectrum ℝ T ⊆ Set.Icc (rayleighInf T) (rayleighSup T) := by
  intro t ht; rw [Set.mem_Icc]; constructor
  · by_contra h; push_neg at h; apply ht
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
      _ (c := ⟨rayleighInf T - t, le_of_lt (sub_pos.mpr h)⟩)
    · exact_mod_cast sub_pos.mpr h
    · intro x; rw [inner_shifted_eq T hT t x, Complex.norm_real, Real.norm_eq_abs]
      simp only [NNReal.coe_mk]
      have := rayleighInf_mul_le_reApplyInnerSelf T x
      rw [abs_of_nonpos (by nlinarith [sq_nonneg ‖x‖])]
      nlinarith [sq_nonneg ‖x‖]
  · by_contra h; push_neg at h; apply ht
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
      _ (c := ⟨t - rayleighSup T, le_of_lt (sub_pos.mpr h)⟩)
    · exact_mod_cast sub_pos.mpr h
    · intro x; rw [inner_shifted_eq T hT t x, Complex.norm_real, Real.norm_eq_abs]
      simp only [NNReal.coe_mk]
      have := reApplyInnerSelf_le_rayleighSup_mul T x
      rw [abs_of_nonneg (by nlinarith [sq_nonneg ‖x‖])]
      nlinarith [sq_nonneg ‖x‖]

omit [CompleteSpace H] in
/-- Discriminant bound for a quadratic in `t`: if `A + 2tB + t²C ≥ 0` for all real `t` and
`C ≥ 0`, then `B² ≤ AC`. Used in proving positivity-derived Cauchy-Schwarz inequalities. -/
lemma discriminant_nonneg_aux {A B C : ℝ} (hC : 0 ≤ C)
    (hquad : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C) :
    B ^ 2 ≤ A * C := by
  by_cases hC0 : C = 0
  · subst hC0; simp only [mul_zero]; rw [sq_nonpos_iff]
    have hlin : ∀ t : ℝ, 0 ≤ A + 2 * t * B := by intro t; linarith [hquad t]
    by_contra hB
    rcases ne_iff_lt_or_gt.mp hB with hBn | hBp
    · obtain ⟨n, hn⟩ := exists_nat_gt (-A / (2 * B))
      rw [div_lt_iff_of_neg (by linarith : 2 * B < 0)] at hn; nlinarith [hlin n]
    · obtain ⟨n, hn⟩ := exists_nat_gt (A / (2 * B))
      rw [div_lt_iff₀ (by linarith : 0 < 2 * B)] at hn; nlinarith [hlin (-(n : ℝ))]
  · have hC_pos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    nlinarith [mul_nonneg (hquad (-B / C)) (le_of_lt hC_pos),
               show (A + 2 * (-B / C) * B + (-B / C) ^ 2 * C) * C = A * C - B ^ 2 from
                 by field_simp; ring]

omit [CompleteSpace H] in
/-- Quadratic expansion of `⟨P(x + tPx), x + tPx⟩` for positive `P`: expressed in `t` as a
quadratic polynomial whose coefficients are `Re⟨Px,x⟩`, `2‖Px‖²` and `Re⟨P²x, Px⟩`. -/
lemma quadratic_expansion_aux
    (P : H →L[ℂ] H) (hP : P.IsPositive) (x : H) (t : ℝ) :
    P.reApplyInnerSelf (x + (t : ℂ) • P x) =
    P.reApplyInnerSelf x + 2 * t * ‖P x‖ ^ 2 + t ^ 2 * P.reApplyInnerSelf (P x) := by
  have hsym := hP.isSymmetric
  have hcast : ∀ y, (P.reApplyInnerSelf y : ℂ) = @inner ℂ H _ (P y) y :=
    fun y => hsym.coe_reApplyInnerSelf_apply y
  have key : ((P.reApplyInnerSelf (x + (t : ℂ) • P x) : ℝ) : ℂ) =
    ((P.reApplyInnerSelf x + 2 * t * ‖P x‖ ^ 2 + t ^ 2 * P.reApplyInnerSelf (P x) : ℝ) : ℂ) := by
    conv_lhs => rw [hcast]
    simp only [map_add, ContinuousLinearMap.map_smul,
               inner_add_left, inner_add_right,
               inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    push_cast
    rw [← hcast x, ← hcast (P x)]
    have h1 : @inner ℂ H _ (P x) (P x) = ((‖P x‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
    have h2 : @inner ℂ H _ (P (P x)) x = ((‖P x‖ : ℝ) : ℂ) ^ 2 := by
      rw [hsym.apply_clm (P x) x]; exact inner_self_eq_norm_sq_to_K _
    rw [h1, h2, hcast x, hcast (P x)]
    ring
  exact_mod_cast key

omit [CompleteSpace H] in
set_option maxHeartbeats 64000000 in
/-- For a positive operator `P`, the Cauchy-Schwarz-type bound `‖Px‖² ≤ ‖P‖ · Re⟨Px, x⟩`.
This is the key inequality used to show that `rayleighInf` lies in the spectrum. -/
lemma norm_sq_le_opNorm_mul_reApplyInnerSelf
    (P : H →L[ℂ] H) (hP : P.IsPositive) (x : H) :
    ‖P x‖ ^ 2 ≤ ‖P‖ * P.reApplyInnerSelf x := by
  by_cases hPx : P x = 0
  · simp only [hPx, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (norm_nonneg _) ((ContinuousLinearMap.isPositive_def.mp hP).2 x)
  have hpos := (ContinuousLinearMap.isPositive_def.mp hP).2

  have hquad : ∀ t : ℝ, 0 ≤ P.reApplyInnerSelf x + 2 * t * ‖P x‖ ^ 2 +
      t ^ 2 * P.reApplyInnerSelf (P x) := by
    intro t; rw [← quadratic_expansion_aux P hP x t]; exact hpos _

  have hdisc := discriminant_nonneg_aux (hpos (P x)) hquad

  have hC_le : P.reApplyInnerSelf (P x) ≤ ‖P‖ * ‖P x‖ ^ 2 := by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    calc RCLike.re (@inner ℂ H _ (P (P x)) (P x))
        ≤ ‖@inner ℂ H _ (P (P x)) (P x)‖ := RCLike.re_le_norm _
      _ ≤ ‖P (P x)‖ * ‖P x‖ := norm_inner_le_norm _ _
      _ ≤ ‖P‖ * ‖P x‖ * ‖P x‖ := by gcongr; exact P.le_opNorm _
      _ = ‖P‖ * ‖P x‖ ^ 2 := by ring
  have hB_pos : (0 : ℝ) < ‖P x‖ ^ 2 := by positivity

  have : (‖P x‖ ^ 2) ^ 2 ≤ P.reApplyInnerSelf x * (‖P‖ * ‖P x‖ ^ 2) := calc
    (‖P x‖ ^ 2) ^ 2 ≤ P.reApplyInnerSelf x * P.reApplyInnerSelf (P x) := hdisc
    _ ≤ P.reApplyInnerSelf x * (‖P‖ * ‖P x‖ ^ 2) := by nlinarith [hpos x]
  rw [sq (‖P x‖ ^ 2)] at this
  exact le_of_mul_le_mul_right (by nlinarith) hB_pos

set_option maxHeartbeats 16000000 in
/-- The infimum of the Rayleigh quotient of a self-adjoint operator on a nontrivial complex
Hilbert space belongs to its real spectrum (Melrose Prop 16.2 / 16.3). -/
theorem selfAdjoint_inf_mem_spectrum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    rayleighInf T ∈ spectrum ℝ T := by
  rw [spectrum.mem_iff]
  intro hu
  set m := rayleighInf T
  set S := algebraMap ℝ (H →L[ℂ] H) m - T
  set P := T - algebraMap ℝ (H →L[ℂ] H) m
  have hP_eq_neg_S : P = -S := neg_sub _ _ |>.symm
  have hP_inner : ∀ x : H, P.reApplyInnerSelf x = T.reApplyInnerSelf x - m * ‖x‖ ^ 2 := by
    intro x
    show (T - algebraMap ℝ (H →L[ℂ] H) m).reApplyInnerSelf x = _
    have halg : algebraMap ℝ (H →L[ℂ] H) m = (m : ℂ) • (1 : H →L[ℂ] H) := by
      simp [Algebra.algebraMap_eq_smul_one]
    simp only [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.sub_apply,
      halg, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      inner_sub_left, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
    simp [sq]
  have hP_nonneg : ∀ x, 0 ≤ P.reApplyInnerSelf x := by
    intro x; rw [hP_inner]; linarith [rayleighInf_mul_le_reApplyInnerSelf T x]
  have hP_sa : IsSelfAdjoint P := hT.sub (IsSelfAdjoint.algebraMap _ (.all m))
  have hP_pos : P.IsPositive :=
    ContinuousLinearMap.isPositive_def.mpr ⟨hP_sa.isSymmetric, hP_nonneg⟩
  have hSx_bound : ∀ x, ‖S x‖ ^ 2 ≤ ‖P‖ * (T.reApplyInnerSelf x - m * ‖x‖ ^ 2) := by
    intro x
    have h1 : ‖S x‖ = ‖P x‖ := by
      rw [hP_eq_neg_S, ContinuousLinearMap.neg_apply, norm_neg]
    rw [h1, ← hP_inner]
    exact norm_sq_le_opNorm_mul_reApplyInnerSelf P hP_pos x
  have hSinv : ∀ x, (↑hu.unit⁻¹ : H →L[ℂ] H) (S x) = x := by
    intro x
    have h : (↑hu.unit⁻¹ : H →L[ℂ] H) * (↑hu.unit : H →L[ℂ] H) = 1 :=
      by exact_mod_cast hu.unit.inv_mul
    have := DFunLike.congr_fun h x
    rwa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
  set C := ‖(↑hu.unit⁻¹ : H →L[ℂ] H)‖
  have hbound : ∀ x, ‖x‖ ≤ C * ‖S x‖ := by
    intro x
    calc ‖x‖ = ‖(↑hu.unit⁻¹ : H →L[ℂ] H) (S x)‖ := by rw [hSinv]
      _ ≤ C * ‖S x‖ := (↑hu.unit⁻¹ : H →L[ℂ] H).le_opNorm _
  by_cases hP_norm : ‖P‖ = 0
  · have hS_zero : S = 0 := neg_eq_zero.mp (hP_eq_neg_S ▸ norm_eq_zero.mp hP_norm)
    exact absurd (hS_zero ▸ hu) (by
      rw [ContinuousLinearMap.isUnit_iff_bijective]
      intro ⟨_, hsurj⟩
      obtain ⟨x, hx⟩ := exists_ne (0 : H)
      obtain ⟨y, hy⟩ := hsurj x; simp at hy; exact hx hy.symm)
  · have hP_pos_norm : 0 < ‖P‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hP_norm)
    haveI : Nonempty {x : H // x ≠ 0} := by
      obtain ⟨x, hx⟩ := exists_ne (0 : H); exact ⟨⟨x, hx⟩⟩
    have hC_pos : 0 < C := by
      by_contra hC; push Not at hC
      obtain ⟨x, hx⟩ := exists_ne (0 : H)
      exact hx (norm_le_zero_iff.mp (le_trans (hbound x)
        (mul_nonpos_of_nonpos_of_nonneg hC (norm_nonneg _))))
    have hε_pos : (0 : ℝ) < 1 / (2 * C ^ 2 * ‖P‖) := by positivity
    obtain ⟨⟨x₀, hx₀_ne⟩, hx₀_lt⟩ := exists_lt_of_ciInf_lt
      (show rayleighInf T < rayleighInf T + 1 / (2 * C ^ 2 * ‖P‖)
       from lt_add_of_pos_right _ hε_pos)
    have hx₀_rq : T.reApplyInnerSelf x₀ < (m + 1 / (2 * C ^ 2 * ‖P‖)) * ‖x₀‖ ^ 2 := by
      rw [ContinuousLinearMap.rayleighQuotient,
        div_lt_iff₀ (show 0 < ‖x₀‖ ^ 2 from by positivity)] at hx₀_lt
      exact hx₀_lt
    have hSx₀_sq : ‖S x₀‖ ^ 2 ≤ ‖P‖ * (1 / (2 * C ^ 2 * ‖P‖)) * ‖x₀‖ ^ 2 := by
      calc ‖S x₀‖ ^ 2 ≤ ‖P‖ * (T.reApplyInnerSelf x₀ - m * ‖x₀‖ ^ 2) := hSx_bound x₀
        _ ≤ ‖P‖ * (1 / (2 * C ^ 2 * ‖P‖) * ‖x₀‖ ^ 2) := by
            nlinarith [hP_nonneg x₀, hP_inner x₀]
        _ = ‖P‖ * (1 / (2 * C ^ 2 * ‖P‖)) * ‖x₀‖ ^ 2 := by ring
    have hx₀_sq : ‖x₀‖ ^ 2 ≤ C ^ 2 * ‖S x₀‖ ^ 2 := by
      nlinarith [hbound x₀, sq_nonneg (C * ‖S x₀‖ - ‖x₀‖),
        norm_nonneg x₀, norm_nonneg (S x₀)]
    have hcombine : ‖x₀‖ ^ 2 ≤ 1 / 2 * ‖x₀‖ ^ 2 := by
      calc ‖x₀‖ ^ 2 ≤ C ^ 2 * ‖S x₀‖ ^ 2 := hx₀_sq
        _ ≤ C ^ 2 * (‖P‖ * (1 / (2 * C ^ 2 * ‖P‖)) * ‖x₀‖ ^ 2) := by
            nlinarith [sq_nonneg C]
        _ = (C ^ 2 * ‖P‖ * (1 / (2 * C ^ 2 * ‖P‖))) * ‖x₀‖ ^ 2 := by ring
        _ = 1 / 2 * ‖x₀‖ ^ 2 := by
            congr 1
            have : (2 : ℝ) * C ^ 2 * ‖P‖ ≠ 0 := by positivity
            field_simp
    linarith [show 0 < ‖x₀‖ ^ 2 from by positivity]


omit [CompleteSpace H] in
/-- Negation symmetry: `rayleighInf (-T) = -rayleighSup T`. -/
lemma rayleighInf_neg (T : H →L[ℂ] H) :
    rayleighInf (-T) = -rayleighSup T := by
  simp only [rayleighInf, rayleighSup, ContinuousLinearMap.rayleighQuotient_neg_apply, iInf, iSup]
  have hrw : (Set.range fun (i : { x : H // x ≠ 0 }) => -T.rayleighQuotient ↑i) =
    -(Set.range fun (i : { x : H // x ≠ 0 }) => T.rayleighQuotient ↑i) := by
    ext x; simp only [Set.mem_range, Set.mem_neg]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, (neg_neg _).symm⟩
    · rintro ⟨i, hi⟩; exact ⟨i, by linarith⟩
  rw [hrw, Real.sInf_neg]

set_option maxHeartbeats 400000 in
/-- The supremum of the Rayleigh quotient of a self-adjoint operator on a nontrivial complex
Hilbert space belongs to its real spectrum, obtained from the infimum statement via
negation. -/
theorem selfAdjoint_sup_mem_spectrum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    rayleighSup T ∈ spectrum ℝ T := by
  have hinf := selfAdjoint_inf_mem_spectrum (-T) hT.neg
  rw [rayleighInf_neg] at hinf
  rw [← spectrum.neg_eq] at hinf
  exact Set.neg_mem_neg.mp hinf

/-- Full Rayleigh quotient characterization (Melrose Prop 16.1–16.3): for a self-adjoint
operator `T` on a nontrivial complex Hilbert space, both `rayleighInf T` and `rayleighSup T`
lie in `spectrum ℝ T`, and `spectrum ℝ T` is contained in `[rayleighInf T, rayleighSup T]`. -/
theorem selfAdjoint_spectrum_Icc_characterization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ({rayleighInf T, rayleighSup T} ⊆ spectrum ℝ T) ∧
    (spectrum ℝ T ⊆ Set.Icc (rayleighInf T) (rayleighSup T)) :=
  ⟨by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact selfAdjoint_inf_mem_spectrum T hT
    · exact selfAdjoint_sup_mem_spectrum T hT,
   selfAdjoint_spectrum_subset_Icc T hT⟩

end SpectralTheorem

end
