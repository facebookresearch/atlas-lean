/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.HasseMinkowski
import Mathlib



/-- A diagonal ternary quadratic form $w_0 x^2 + w_1 y^2 + w_2 z^2$ is isotropic over $\mathbb{Q}$ iff there is a nontrivial rational solution $(x, y, z)$ with $w_0 x^2 + w_1 y^2 + w_2 z^2 = 0$. -/
lemma ternary_isIsotropic_iff (w : Fin 3 → ℚ) :
    (diagQuadForm 3 w).IsIsotropic ↔
    ∃ x y z : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      w 0 * x ^ 2 + w 1 * y ^ 2 + w 2 * z ^ 2 = 0 := by
  unfold diagQuadForm QuadraticMap.IsIsotropic
  constructor
  · rintro ⟨v, hne, hQ⟩
    refine ⟨v 0, v 1, v 2, ?_, ?_⟩
    · intro ⟨h0, h1, h2⟩
      apply hne; ext i; fin_cases i <;> assumption
    · simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
        Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hQ
      have hQ' : w 0 * (v 0 * v 0) + (w 1 * (v 1 * v 1) + w 2 * (v 2 * v 2)) = 0 := by
        convert hQ using 2
      nlinarith [sq (v 0), sq (v 1), sq (v 2)]
  · rintro ⟨x, y, z, hne, heq⟩
    refine ⟨![x, y, z], ?_, ?_⟩
    · intro h
      apply hne
      exact ⟨by have := congr_fun h 0; simp at this; exact this,
             by have := congr_fun h 1; simp at this; exact this,
             by have := congr_fun h 2; simp at this; exact this⟩
    · simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
          Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero]
      show w 0 * (x * x) + (w 1 * (y * y) + w 2 * (z * z)) = 0
      nlinarith [sq x, sq y, sq z]

set_option maxHeartbeats 400000 in

/-- Real isotropy for Legendre: the diagonal form $ax^2 + by^2 + cz^2$ has a nontrivial real solution iff $a, b, c$ do not all have the same sign. -/
lemma legendre_real_isotropic (a b c : ℤ)
    (hsign : ¬(0 < a ∧ 0 < b ∧ 0 < c) ∧ ¬(a < 0 ∧ b < 0 ∧ c < 0)) :
    (diagQuadFormOver ℝ 3 ![(↑a : ℚ), ↑b, ↑c]).IsIsotropic := by
  obtain ⟨h1, h2⟩ := hsign
  push Not at h1 h2


  rcases (show a = 0 ∨ 0 < a ∨ a < 0 from by omega) with ha0 | hap | han
  ·
    refine ⟨fun i => match i with | 0 => 1 | 1 => 0 | 2 => 0, ?_, ?_⟩
    · intro h; have := congr_fun h 0; simp at this
    · unfold diagQuadFormOver
      simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
        Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero]
      show algebraMap ℚ ℝ ↑a * (1 * 1) +
        (algebraMap ℚ ℝ ↑b * (0 * 0) + algebraMap ℚ ℝ ↑c * (0 * 0)) = 0
      simp [ha0]
  ·
    rcases (show b = 0 ∨ 0 < b ∨ b < 0 from by omega) with hb0 | hbp | hbn
    ·
      refine ⟨fun i => match i with | 0 => 0 | 1 => 1 | 2 => 0, ?_, ?_⟩
      · intro h; have := congr_fun h 1; simp at this
      · unfold diagQuadFormOver
        simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
          Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero]
        show algebraMap ℚ ℝ ↑a * (0 * 0) +
          (algebraMap ℚ ℝ ↑b * (1 * 1) + algebraMap ℚ ℝ ↑c * (0 * 0)) = 0
        simp [hb0]
    ·
      have hc0 : c ≤ 0 := h1 hap hbp
      rcases eq_or_lt_of_le hc0 with hc_eq | hcn
      ·
        refine ⟨fun i => match i with | 0 => 0 | 1 => 0 | 2 => 1, ?_, ?_⟩
        · intro h; have := congr_fun h 2; simp at this
        · unfold diagQuadFormOver
          simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
            Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero]
          show algebraMap ℚ ℝ ↑a * (0 * 0) +
            (algebraMap ℚ ℝ ↑b * (0 * 0) + algebraMap ℚ ℝ ↑c * (1 * 1)) = 0
          simp [hc_eq.symm]
      ·

        refine ⟨fun i => match i with | 0 => 0 | 1 => Real.sqrt (-(c : ℝ)) | 2 => Real.sqrt (b : ℝ), ?_, ?_⟩
        · intro h
          have : Real.sqrt (-(c : ℝ)) = 0 := by have := congr_fun h 1; simp at this; exact this
          exact (Real.sqrt_pos.mpr (by exact_mod_cast neg_pos.mpr hcn : (0 : ℝ) < -(↑c : ℝ))).ne' this
        · unfold diagQuadFormOver
          simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
            Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero]
          show algebraMap ℚ ℝ ↑a * (0 * 0) +
            (algebraMap ℚ ℝ ↑b * (Real.sqrt (-(↑c : ℝ)) * Real.sqrt (-(↑c : ℝ))) +
             algebraMap ℚ ℝ ↑c * (Real.sqrt (↑b : ℝ) * Real.sqrt (↑b : ℝ))) = 0
          rw [Real.mul_self_sqrt (show (0 : ℝ) ≤ -(↑c : ℝ) from by exact_mod_cast neg_nonneg.mpr hcn.le)]
          rw [Real.mul_self_sqrt (show (0 : ℝ) ≤ (↑b : ℝ) from by exact_mod_cast hbp.le)]
          simp; ring
    ·

      refine ⟨fun i => match i with | 0 => Real.sqrt (-(b : ℝ)) | 1 => Real.sqrt (a : ℝ) | 2 => 0, ?_, ?_⟩
      · intro h
        have : Real.sqrt (-(b : ℝ)) = 0 := by have := congr_fun h 0; simp at this; exact this
        exact (Real.sqrt_pos.mpr (by exact_mod_cast neg_pos.mpr hbn : (0 : ℝ) < -(↑b : ℝ))).ne' this
      · unfold diagQuadFormOver
        simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
          Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero]
        show algebraMap ℚ ℝ ↑a * (Real.sqrt (-(↑b : ℝ)) * Real.sqrt (-(↑b : ℝ))) +
          (algebraMap ℚ ℝ ↑b * (Real.sqrt (↑a : ℝ) * Real.sqrt (↑a : ℝ)) +
           algebraMap ℚ ℝ ↑c * (0 * 0)) = 0
        rw [Real.mul_self_sqrt (show (0 : ℝ) ≤ -(↑b : ℝ) from by exact_mod_cast neg_nonneg.mpr hbn.le)]
        rw [Real.mul_self_sqrt (show (0 : ℝ) ≤ (↑a : ℝ) from by exact_mod_cast hap.le)]
        simp; ring
  ·
    rcases (show b = 0 ∨ 0 < b ∨ b < 0 from by omega) with hb0 | hbp | hbn
    ·
      refine ⟨fun i => match i with | 0 => 0 | 1 => 1 | 2 => 0, ?_, ?_⟩
      · intro h; have := congr_fun h 1; simp at this
      · unfold diagQuadFormOver
        simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
          Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero]
        show algebraMap ℚ ℝ ↑a * (0 * 0) +
          (algebraMap ℚ ℝ ↑b * (1 * 1) + algebraMap ℚ ℝ ↑c * (0 * 0)) = 0
        simp [hb0]
    ·

      refine ⟨fun i => match i with | 0 => Real.sqrt (b : ℝ) | 1 => Real.sqrt (-(a : ℝ)) | 2 => 0, ?_, ?_⟩
      · intro h
        have : Real.sqrt (b : ℝ) = 0 := by have := congr_fun h 0; simp at this; exact this
        exact (Real.sqrt_pos.mpr (by exact_mod_cast hbp : (0 : ℝ) < (↑b : ℝ))).ne' this
      · unfold diagQuadFormOver
        simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
          Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero]
        show algebraMap ℚ ℝ ↑a * (Real.sqrt (↑b : ℝ) * Real.sqrt (↑b : ℝ)) +
          (algebraMap ℚ ℝ ↑b * (Real.sqrt (-(↑a : ℝ)) * Real.sqrt (-(↑a : ℝ))) +
           algebraMap ℚ ℝ ↑c * (0 * 0)) = 0
        rw [Real.mul_self_sqrt (show (0 : ℝ) ≤ (↑b : ℝ) from by exact_mod_cast hbp.le)]
        rw [Real.mul_self_sqrt (show (0 : ℝ) ≤ -(↑a : ℝ) from by exact_mod_cast neg_nonneg.mpr han.le)]
        simp; ring
    ·
      have hc0 : 0 ≤ c := h2 han hbn
      rcases eq_or_lt_of_le hc0 with hc_eq | hcp
      ·
        refine ⟨fun i => match i with | 0 => 0 | 1 => 0 | 2 => 1, ?_, ?_⟩
        · intro h; have := congr_fun h 2; simp at this
        · unfold diagQuadFormOver
          simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
            Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero]
          show algebraMap ℚ ℝ ↑a * (0 * 0) +
            (algebraMap ℚ ℝ ↑b * (0 * 0) + algebraMap ℚ ℝ ↑c * (1 * 1)) = 0
          simp [← hc_eq]
      ·

        refine ⟨fun i => match i with | 0 => Real.sqrt (c : ℝ) | 1 => 0 | 2 => Real.sqrt (-(a : ℝ)), ?_, ?_⟩
        · intro h
          have : Real.sqrt (c : ℝ) = 0 := by have := congr_fun h 0; simp at this; exact this
          exact (Real.sqrt_pos.mpr (by exact_mod_cast hcp : (0 : ℝ) < (↑c : ℝ))).ne' this
        · unfold diagQuadFormOver
          simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
            Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero]
          show algebraMap ℚ ℝ ↑a * (Real.sqrt (↑c : ℝ) * Real.sqrt (↑c : ℝ)) +
            (algebraMap ℚ ℝ ↑b * (0 * 0) +
             algebraMap ℚ ℝ ↑c * (Real.sqrt (-(↑a : ℝ)) * Real.sqrt (-(↑a : ℝ)))) = 0
          rw [Real.mul_self_sqrt (show (0 : ℝ) ≤ (↑c : ℝ) from by exact_mod_cast hcp.le)]
          rw [Real.mul_self_sqrt (show (0 : ℝ) ≤ -(↑a : ℝ) from by exact_mod_cast neg_nonneg.mpr han.le)]
          simp; ring

set_option maxHeartbeats 800000 in
/-- Hensel-lifting square root: if $-uv$ is a square mod $w$, and an odd prime $p$ divides $w$ but not $u, v$, then $-uv$ is a square in $\mathbb{Q}_p$. -/
theorem neg_product_has_padic_sqrt_of_cong
    (u v w : ℤ) (p : ℕ) [hp : Fact p.Prime]
    (hcop_wu : IsCoprime w u) (hcop_wv : IsCoprime w v)
    (hcong : ∃ x : ℤ, x ^ 2 ≡ -(u * v) [ZMOD w])
    (hdvd : (p : ℤ) ∣ w)
    (hodd : p ≠ 2) :
    ∃ t : ℚ_[p], t ^ 2 = -(algebraMap ℚ ℚ_[p] (↑u) * algebraMap ℚ ℚ_[p] (↑v)) := by
  open Polynomial in

    obtain ⟨x, hx⟩ := hcong

    have hmod_p : x ^ 2 ≡ -(u * v) [ZMOD (p : ℤ)] := hx.of_dvd hdvd
    have hdvd_sum : (p : ℤ) ∣ (x ^ 2 + u * v) := by
      rwa [Int.modEq_iff_dvd, show -(u * v) - x ^ 2 = -(x ^ 2 + u * v) from by ring,
           dvd_neg] at hmod_p

    have hcop_pu : IsCoprime (p : ℤ) u := hcop_wu.of_isCoprime_of_dvd_left hdvd
    have hcop_pv : IsCoprime (p : ℤ) v := hcop_wv.of_isCoprime_of_dvd_left hdvd

    have hcop_px : IsCoprime x (p : ℤ) := by
      by_contra h
      have hp_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
      have hpx : (p : ℤ) ∣ x := by
        by_contra hndvd; exact h (hp_prime.coprime_iff_not_dvd.mpr hndvd).symm
      have hpuv : (p : ℤ) ∣ u * v := by
        have := dvd_sub hdvd_sum (dvd_pow hpx (by norm_num : (2 : ℕ) ≠ 0))
        rwa [show x ^ 2 + u * v - x ^ 2 = u * v from by ring] at this
      have hcop := (hcop_pu.mul_right hcop_pv).isUnit_of_dvd' dvd_rfl hpuv
      rw [Int.isUnit_iff] at hcop
      rcases hcop with h | h <;> (have := hp.out.one_lt; omega)

    let F : Polynomial ℤ_[p] := X ^ 2 + C ((u * v : ℤ) : ℤ_[p])
    let a₀ : ℤ_[p] := (x : ℤ_[p])

    have hFa : F.aeval a₀ = ((x ^ 2 + u * v : ℤ) : ℤ_[p]) := by
      simp only [F, a₀, aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
                 Algebra.algebraMap_self_apply]; push_cast; ring
    have hFa_lt : ‖F.aeval a₀‖ < 1 := by
      rw [hFa]; exact (PadicInt.norm_int_lt_one_iff_dvd _).mpr hdvd_sum

    have hF'a_eq : ‖F.derivative.aeval a₀‖ = 1 := by
      have hF'a : F.derivative.aeval a₀ = 2 * a₀ := by
        simp only [F, derivative_add, derivative_pow, derivative_X, derivative_C,
                   aeval_def, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
                   Algebra.algebraMap_self_apply, eval₂_zero, eval₂_one]; ring
      rw [hF'a]; show ‖(2 * x : ℤ_[p])‖ = 1
      rw [show (2 * x : ℤ_[p]) = ((2 * x : ℤ) : ℤ_[p]) from by push_cast; ring]
      rw [PadicInt.norm_intCast_eq_one_iff]
      exact IsCoprime.mul_left (by
        have : Nat.Coprime 2 p := Nat.Coprime.symm (hp.out.coprime_iff_not_dvd.mpr (fun h =>
          hodd (Nat.le_of_dvd (by omega) h |>.antisymm hp.out.two_le)))
        exact_mod_cast this) hcop_px

    have hlt : ‖F.aeval a₀‖ < ‖F.derivative.aeval a₀‖ ^ 2 := by
      rw [hF'a_eq]; simp; exact hFa_lt

    obtain ⟨z, hz, _, _, _⟩ := hensels_lemma hlt

    have hroot : z ^ 2 + ((u * v : ℤ) : ℤ_[p]) = 0 := by
      simp only [F, aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
                 Algebra.algebraMap_self_apply] at hz; exact hz

    exact ⟨z, by
      have hz2 : z ^ 2 = -((u * v : ℤ) : ℤ_[p]) := by linear_combination hroot
      have h1 : ((z : ℚ_[p])) ^ 2 = ((z ^ 2 : ℤ_[p]) : ℚ_[p]) := by push_cast; ring
      rw [h1, hz2]; simp [PadicInt.coe_intCast, PadicInt.coe_neg]⟩

/-- A nonzero integer maps to a nonzero element of $\mathbb{Q}_p$. -/
lemma algebraMap_intCast_ne_zero' {p : ℕ} [Fact p.Prime] (n : ℤ) (hn : n ≠ 0) :
    algebraMap ℚ ℚ_[p] (↑n) ≠ 0 := by
  simp only [ne_eq, map_eq_zero]; exact Int.cast_ne_zero.mpr hn

/-- Unfolding the ternary diagonal quadratic form over $\mathbb{Q}_p$ at the vector $(v_0, v_1, v_2)$ in terms of the underlying multiplication expression. -/
lemma eval_diagQuadFormOver_3 {p : ℕ} [Fact p.Prime]
    (q₀ q₁ q₂ : ℚ) (v₀ v₁ v₂ : ℚ_[p])
    (h : algebraMap ℚ ℚ_[p] q₀ * (v₀ * v₀) + algebraMap ℚ ℚ_[p] q₁ * (v₁ * v₁) +
         algebraMap ℚ ℚ_[p] q₂ * (v₂ * v₂) = 0) :
    (diagQuadFormOver ℚ_[p] 3 ![q₀, q₁, q₂]) ![v₀, v₁, v₂] = 0 := by
  simp only [diagQuadFormOver, QuadraticMap.weightedSumSquares_apply, Algebra.smul_def,
             Fin.sum_univ_three, Algebra.algebraMap_self_apply,
             show (fun i => algebraMap ℚ ℚ_[p] (![q₀, q₁, q₂] i)) 0 = algebraMap ℚ ℚ_[p] q₀ from rfl,
             show (fun i => algebraMap ℚ ℚ_[p] (![q₀, q₁, q₂] i)) 1 = algebraMap ℚ ℚ_[p] q₁ from rfl,
             show (fun i => algebraMap ℚ ℚ_[p] (![q₀, q₁, q₂] i)) 2 = algebraMap ℚ ℚ_[p] q₂ from rfl,
             show (![v₀, v₁, v₂] : Fin 3 → ℚ_[p]) 0 = v₀ from rfl,
             show (![v₀, v₁, v₂] : Fin 3 → ℚ_[p]) 1 = v₁ from rfl,
             show (![v₀, v₁, v₂] : Fin 3 → ℚ_[p]) 2 = v₂ from rfl]; exact h

/-- $p$-adic isotropy at an odd prime $p$ dividing one of $a, b, c$: Legendre's congruence conditions imply isotropy over $\mathbb{Q}_p$. -/
theorem legendre_padic_isotropic_at_dividing_prime (a b c : ℤ)
    (ha : Squarefree a) (hb : Squarefree b) (hc : Squarefree c)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c)
    (hX : ∃ X : ℤ, X ^ 2 ≡ -b * c [ZMOD a])
    (hY : ∃ Y : ℤ, Y ^ 2 ≡ -c * a [ZMOD b])
    (hZ : ∃ Z : ℤ, Z ^ 2 ≡ -a * b [ZMOD c])
    (p : ℕ) [Fact p.Prime]
    (hdvd : (p : ℤ) ∣ a ∨ (p : ℤ) ∣ b ∨ (p : ℤ) ∣ c)
    (hp_odd : p ≠ 2) :
    (diagQuadFormOver ℚ_[p] 3 ![(↑a : ℚ), ↑b, ↑c]).IsIsotropic := by

  have hX' : ∃ X : ℤ, X ^ 2 ≡ -(b * c) [ZMOD a] := by
    obtain ⟨X, hX⟩ := hX; exact ⟨X, by rwa [show -(b * c) = -b * c from by ring]⟩
  have hY' : ∃ Y : ℤ, Y ^ 2 ≡ -(a * c) [ZMOD b] := by
    obtain ⟨Y, hY⟩ := hY; exact ⟨Y, by rwa [show -(a * c) = -c * a from by ring]⟩
  have hZ' : ∃ Z : ℤ, Z ^ 2 ≡ -(a * b) [ZMOD c] := by
    obtain ⟨Z, hZ⟩ := hZ; exact ⟨Z, by rwa [show -(a * b) = -a * b from by ring]⟩
  rcases hdvd with hdvd_a | hdvd_b | hdvd_c
  ·

    obtain ⟨t, ht⟩ := neg_product_has_padic_sqrt_of_cong b c a p hab hac hX' hdvd_a hp_odd
    refine ⟨![0, algebraMap ℚ ℚ_[p] ↑c, t], ?_, ?_⟩
    · intro h; exact algebraMap_intCast_ne_zero' c (Squarefree.ne_zero hc) (congr_fun h 1)
    · exact eval_diagQuadFormOver_3 _ _ _ _ _ _
        (by rw [show t * t = t ^ 2 from (sq t).symm, ht]; ring)
  ·

    obtain ⟨t, ht⟩ := neg_product_has_padic_sqrt_of_cong a c b p hab.symm hbc hY' hdvd_b hp_odd
    refine ⟨![algebraMap ℚ ℚ_[p] ↑c, 0, t], ?_, ?_⟩
    · intro h; exact algebraMap_intCast_ne_zero' c (Squarefree.ne_zero hc) (congr_fun h 0)
    · exact eval_diagQuadFormOver_3 _ _ _ _ _ _
        (by rw [show t * t = t ^ 2 from (sq t).symm, ht]; ring)
  ·

    obtain ⟨t, ht⟩ := neg_product_has_padic_sqrt_of_cong a b c p hac.symm hbc.symm hZ' hdvd_c hp_odd
    refine ⟨![algebraMap ℚ ℚ_[p] ↑b, t, 0], ?_, ?_⟩
    · intro h; exact algebraMap_intCast_ne_zero' b (Squarefree.ne_zero hb) (congr_fun h 0)
    · exact eval_diagQuadFormOver_3 _ _ _ _ _ _
        (by rw [show t * t = t ^ 2 from (sq t).symm, ht]; ring)







/-- Auxiliary necessity lemma: from a nontrivial integer solution to $aP^2 + bQ^2 + cR^2 = 0$ (with $a$ squarefree, $\gcd(a, c) = 1$) one extracts an integer $X$ with $X^2 \equiv -bc \pmod{a}$. Proved by strong induction on $|P| + |Q| + |R|$, descending via prime factors. -/
lemma legendre_necessity_mod_sq_aux (a b c : ℤ)
    (ha : Squarefree a) (hac : IsCoprime a c) :
    ∀ n : ℕ, ∀ P Q R : ℤ, P.natAbs + Q.natAbs + R.natAbs = n →
    ¬(P = 0 ∧ Q = 0 ∧ R = 0) → a * P ^ 2 + b * Q ^ 2 + c * R ^ 2 = 0 →
    ∃ X : ℤ, X ^ 2 ≡ -b * c [ZMOD a] := by
  intro n; induction n using Nat.strongRecOn with
  | _ n ih =>
    intro P Q R hn hne heq
    by_cases hprim : ∀ p : ℤ, Prime p → p ∣ P → p ∣ Q → p ∣ R → False
    ·

      have hcop : IsCoprime Q a := by
        apply isCoprime_of_prime_dvd
        · intro ⟨_, ha0⟩; exact not_squarefree_zero (ha0 ▸ ha)
        · intro p hp hpQ hpa
          have hpc := hac.of_isCoprime_of_dvd_left hpa
          have hdvd_p : p ∣ b * Q ^ 2 + c * R ^ 2 := dvd_trans hpa ⟨-P ^ 2, by linarith⟩
          have hpcR2 : p ∣ c * R ^ 2 := by
            have := dvd_sub hdvd_p (dvd_mul_of_dvd_right (dvd_pow hpQ (by norm_num : 2 ≠ 0)) b)
            simp only [add_sub_cancel_left] at this; exact this
          have hpR := hp.dvd_of_dvd_pow (hpc.dvd_of_dvd_mul_left hpcR2)
          have hp2 : p ^ 2 ∣ a * P ^ 2 := by
            rw [show a * P ^ 2 = -(b * Q ^ 2 + c * R ^ 2) from by linarith]
            exact dvd_neg.mpr (dvd_add (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpQ 2) b)
                      (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpR 2) c))
          obtain ⟨a', ha'⟩ := hpa
          have hna' : ¬(p ∣ a') :=
            fun ⟨k, hk⟩ => hp.not_unit (ha p ⟨k, by rw [ha', hk]; ring⟩)
          have hpa'P2 : p ∣ a' * P ^ 2 := by
            rw [ha'] at hp2
            rw [sq, ← show p * (a' * P ^ 2) = p * a' * P ^ 2 from by ring] at hp2
            exact (mul_dvd_mul_iff_left hp.ne_zero).mp hp2
          exact hprim p hp
            (hp.dvd_of_dvd_pow
              ((hp.coprime_iff_not_dvd.mpr hna').dvd_of_dvd_mul_left hpa'P2))
            hpQ hpR

      obtain ⟨u, v, huv⟩ := hcop
      refine ⟨c * R * u, Int.modEq_iff_dvd.mpr ?_⟩
      obtain ⟨k, hk⟩ : a ∣ b * Q ^ 2 + c * R ^ 2 := ⟨-P ^ 2, by linarith⟩
      have h1 : 1 - Q ^ 2 * u ^ 2 = a * (2 * v - v ^ 2 * a) := by
        nlinarith [sq_nonneg (u * Q), sq_nonneg (v * a)]
      have key : a ∣ (b + c * R ^ 2 * u ^ 2) := by
        rw [show b + c * R ^ 2 * u ^ 2 = b * (1 - Q ^ 2 * u ^ 2) + a * k * u ^ 2 from by
          nlinarith [show c * R ^ 2 = a * k - b * Q ^ 2 from by linarith], h1]
        exact ⟨b * (2 * v - v ^ 2 * a) + k * u ^ 2, by ring⟩
      rw [show -b * c - (c * R * u) ^ 2 = -c * (b + c * R ^ 2 * u ^ 2) from by ring, neg_mul]
      exact dvd_neg.mpr (dvd_mul_of_dvd_right key c)
    ·
      have ⟨p, hp, hpP, hpQ, hpR⟩ : ∃ p, Prime p ∧ p ∣ P ∧ p ∣ Q ∧ p ∣ R := by
        by_contra h; exact hprim fun p hp hpP hpQ hpR => h ⟨p, hp, hpP, hpQ, hpR⟩
      obtain ⟨P', rfl⟩ := hpP; obtain ⟨Q', rfl⟩ := hpQ; obtain ⟨R', rfl⟩ := hpR
      have hne' : ¬(P' = 0 ∧ Q' = 0 ∧ R' = 0) :=
        fun ⟨h1, h2, h3⟩ => hne ⟨by simp [h1], by simp [h2], by simp [h3]⟩
      have heq' : a * P' ^ 2 + b * Q' ^ 2 + c * R' ^ 2 = 0 := by
        have : p ^ 2 * (a * P' ^ 2 + b * Q' ^ 2 + c * R' ^ 2) = 0 := by nlinarith
        exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hp.ne_zero)
      refine ih _ ?_ P' Q' R' rfl hne' heq'
      rw [← hn]; simp only [Int.natAbs_mul]
      have hp2 : 2 ≤ p.natAbs := by
        have : p.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hp.ne_zero
        have : p.natAbs ≠ 1 := fun h => hp.not_unit (Int.isUnit_iff_natAbs_eq.mpr h)
        omega
      have hpos : 0 < P'.natAbs + Q'.natAbs + R'.natAbs := by
        by_contra h; push_neg at h
        exact hne' ⟨Int.natAbs_eq_zero.mp (by omega), Int.natAbs_eq_zero.mp (by omega),
                     Int.natAbs_eq_zero.mp (by omega)⟩
      nlinarith

/-- Necessity direction of Legendre's theorem: a nontrivial rational solution to $ax^2 + by^2 + cz^2 = 0$ implies the three congruence conditions (clearing denominators reduces to the auxiliary lemma). -/
lemma legendre_necessity (a b c : ℤ)
    (ha : Squarefree a) (hb : Squarefree b) (hc : Squarefree c)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c)
    (x y z : ℚ) (hne : ¬(x = 0 ∧ y = 0 ∧ z = 0))
    (heq : ↑a * x ^ 2 + ↑b * y ^ 2 + ↑c * z ^ 2 = 0) :
    (∃ X : ℤ, X ^ 2 ≡ -b * c [ZMOD a]) ∧
    (∃ Y : ℤ, Y ^ 2 ≡ -c * a [ZMOD b]) ∧
    (∃ Z : ℤ, Z ^ 2 ≡ -a * b [ZMOD c]) := by

  set P := x.num * (y.den : ℤ) * (z.den : ℤ)
  set Q := y.num * (x.den : ℤ) * (z.den : ℤ)
  set R := z.num * (x.den : ℤ) * (y.den : ℤ)
  have hxd : (x.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp x.den_pos)
  have hyd : (y.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp y.den_pos)
  have hzd : (z.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp z.den_pos)
  have hne_int : ¬(P = 0 ∧ Q = 0 ∧ R = 0) := by
    simp only [P, Q, R]; intro ⟨hP0, hQ0, hR0⟩; apply hne
    have gn : ∀ (q : ℚ) (d1 d2 : ℤ), d1 ≠ 0 → d2 ≠ 0 → q.num * d1 * d2 = 0 → q = 0 :=
      fun q d1 d2 hd1 hd2 h => Rat.num_eq_zero.mp (by
        rcases mul_eq_zero.mp h with h | h
        · exact (mul_eq_zero.mp h).elim id (absurd · hd1)
        · exact absurd h hd2)
    exact ⟨gn x _ _ hyd hzd hP0, gn y _ _ hxd hzd hQ0, gn z _ _ hxd hyd hR0⟩
  have heq_int : a * P ^ 2 + b * Q ^ 2 + c * R ^ 2 = 0 := by
    simp only [P, Q, R]
    suffices h : ((a * (x.num * ↑y.den * ↑z.den) ^ 2 + b * (y.num * ↑x.den * ↑z.den) ^ 2 +
      c * (z.num * ↑x.den * ↑y.den) ^ 2 : ℤ) : ℚ) = 0 by exact_mod_cast h
    push_cast
    have hx : (x.num : ℚ) = x * x.den := by
      have := Rat.num_div_den x; field_simp at this ⊢; linarith
    have hy : (y.num : ℚ) = y * y.den := by
      have := Rat.num_div_den y; field_simp at this ⊢; linarith
    have hz : (z.num : ℚ) = z * z.den := by
      have := Rat.num_div_den z; field_simp at this ⊢; linarith
    rw [hx, hy, hz, show ↑a * (x * ↑x.den * ↑y.den * ↑z.den) ^ 2 +
      ↑b * (y * ↑y.den * ↑x.den * ↑z.den) ^ 2 + ↑c * (z * ↑z.den * ↑x.den * ↑y.den) ^ 2 =
      (↑x.den * ↑y.den * ↑z.den) ^ 2 * (↑a * x ^ 2 + ↑b * y ^ 2 + ↑c * z ^ 2) from by ring,
      heq, mul_zero]

  set n := P.natAbs + Q.natAbs + R.natAbs
  refine ⟨legendre_necessity_mod_sq_aux a b c ha hac n P Q R rfl hne_int heq_int, ?_, ?_⟩
  ·
    obtain ⟨Y, hY⟩ := legendre_necessity_mod_sq_aux b a c hb hbc
      (Q.natAbs + P.natAbs + R.natAbs) Q P R rfl
      (fun ⟨h1, h2, h3⟩ => hne_int ⟨h2, h1, h3⟩) (by linarith)
    exact ⟨Y, by rwa [show -c * a = -a * c from by ring]⟩
  ·
    exact legendre_necessity_mod_sq_aux c a b hc hbc.symm
      (R.natAbs + P.natAbs + Q.natAbs) R P Q rfl
      (fun ⟨h1, h2, h3⟩ => hne_int ⟨h2, h3, h1⟩) (by linarith)


noncomputable section

open QuadraticForm QuadraticMap Module

variable {K : Type*} [Field K]

/-- In a field $K$ with $\operatorname{char}(K) \neq 2$, the element $2$ is invertible. -/
@[reducible]
def invertibleTwoOfRingCharNeTwo (hK : ringChar K ≠ 2) : Invertible (2 : K) := by
  apply invertibleOfRingCharNotDvd
  intro (h : ringChar K ∣ 2)
  apply hK
  have hle : ringChar K ≤ 2 := Nat.le_of_dvd (by omega) h
  have hne0 : ringChar K ≠ 0 := by
    intro h0; rw [h0] at h; exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) h
  have hne1 : ringChar K ≠ 1 := by
    intro h1; exact not_subsingleton K (ringChar.ringChar_eq_one.mp h1)
  omega

variable [Invertible (2 : K)]

/-- A quadratic form $Q$ is geometrically irreducible if its associated bilinear form is left-nondegenerate (separating). This makes the associated conic absolutely irreducible. -/
def QuadraticForm.IsGeometricallyIrreducible
    {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : Prop :=
  (associated (R := K) Q).SeparatingLeft

/-- The quadratic form $ax^2 + by^2 + cz^2 + dxy + exz + fyz$ on $K^3$, encoded as the matrix $\begin{pmatrix} a & d/2 & e/2 \\ d/2 & b & f/2 \\ e/2 & f/2 & c \end{pmatrix}$. -/
def generalConicQuadForm (a b c d e f : K) : QuadraticForm K (Fin 3 → K) :=
  Matrix.toQuadraticMap' !![a, d/2, e/2; d/2, b, f/2; e/2, f/2, c]


/-- Theorem 2.1 (diagonalization): any nondegenerate general conic over a field with $\operatorname{char} \neq 2$ is equivalent to a diagonal weighted sum of squares with nonzero (unit) coefficients. -/
theorem general_conic_diagonalizes_units (a b c d e f : K)
    (hnd : (associated (R := K) (generalConicQuadForm a b c d e f)).SeparatingLeft) :
    ∃ w : Fin (finrank K (Fin 3 → K)) → Kˣ,
      Equivalent (generalConicQuadForm a b c d e f)
        (weightedSumSquares K (fun i => (w i : K))) :=
  (generalConicQuadForm a b c d e f).equivalent_weightedSumSquares_units_of_nondegenerate' hnd


/-- Alias for `generalConicQuadForm`: the general ternary quadratic form $ax^2 + by^2 + cz^2 + dxy + exz + fyz$. -/
def generalConicForm (a b c d e f : K) : QuadraticForm K (Fin 3 → K) :=
  Matrix.toQuadraticMap' !![a, d/2, e/2; d/2, b, f/2; e/2, f/2, c]


section Theorem23

variable {K : Type*} [Field K]

/-- Stereographic projection (forward map): given a base point $(x_0, y_0, z_0)$ on the diagonal conic $aX^2 + bY^2 + cZ^2 = 0$, this maps $(U, V) \in \mathbb{P}^1$ to a point on the conic via a quadratic formula. -/
def stereoForward (a b x₀ y₀ z₀ U V : K) : Fin 3 → K := fun i =>
  match i with
  | 0 => a * x₀ * U ^ 2 + 2 * b * y₀ * U * V - b * x₀ * V ^ 2
  | 1 => -(a * y₀) * U ^ 2 + 2 * a * x₀ * U * V + b * y₀ * V ^ 2
  | 2 => -(a * z₀) * U ^ 2 - b * z₀ * V ^ 2

/-- Stereographic projection (backward map): given a point $v = (X, Y, Z)$ on the conic, projects from the base point $(x_0, y_0, z_0)$ to a point in $\mathbb{P}^1$. -/
def stereoBackward (x₀ y₀ z₀ : K) (v : Fin 3 → K) : Fin 2 → K := fun i =>
  match i with
  | 0 => v 0 * z₀ - x₀ * v 2
  | 1 => v 1 * z₀ - y₀ * v 2

/-- The stereographic forward map indeed lands on the conic: $a \cdot \varphi_0^2 + b \cdot \varphi_1^2 + c \cdot \varphi_2^2 = 0$. -/
theorem stereoForward_on_conic (a b c x₀ y₀ z₀ U V : K)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0) :
    a * (stereoForward a b x₀ y₀ z₀ U V 0) ^ 2 +
    b * (stereoForward a b x₀ y₀ z₀ U V 1) ^ 2 +
    c * (stereoForward a b x₀ y₀ z₀ U V 2) ^ 2 = 0 := by
  simp only [stereoForward]
  linear_combination (a * U ^ 2 + b * V ^ 2) ^ 2 * hpt

/-- Composition identity (0-th coordinate): the back-then-forward of $(U, V)$ scales $U$ by the linear factor $2 z_0 (a x_0 U + b y_0 V)$. -/
theorem stereo_bwd_fwd_0 (a b x₀ y₀ z₀ U V : K) :
    stereoBackward x₀ y₀ z₀ (stereoForward a b x₀ y₀ z₀ U V) 0 =
    2 * z₀ * (a * x₀ * U + b * y₀ * V) * U := by
  simp only [stereoBackward, stereoForward]; ring

/-- Composition identity (1st coordinate): the back-then-forward of $(U, V)$ scales $V$ by the same linear factor $2 z_0 (a x_0 U + b y_0 V)$. -/
theorem stereo_bwd_fwd_1 (a b x₀ y₀ z₀ U V : K) :
    stereoBackward x₀ y₀ z₀ (stereoForward a b x₀ y₀ z₀ U V) 1 =
    2 * z₀ * (a * x₀ * U + b * y₀ * V) * V := by
  simp only [stereoBackward, stereoForward]; ring

/-- Composition identity (forward-then-backward, 0-th coordinate): the forward image of the backward projection of a point $(x, y, z)$ on the conic returns $x$ scaled by the bilinear pairing factor. -/
theorem stereo_fwd_bwd_0 (a b c x₀ y₀ z₀ x y z : K)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0)
    (honC : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) :
    stereoForward a b x₀ y₀ z₀ (x * z₀ - x₀ * z) (y * z₀ - y₀ * z) 0 =
    2 * z₀ ^ 2 * (a * x₀ * x + b * y₀ * y + c * z₀ * z) * x := by
  simp only [stereoForward]
  linear_combination (x₀ * z ^ 2 - 2 * x * z * z₀) * hpt - x₀ * z₀ ^ 2 * honC

/-- Composition identity (forward-then-backward, 1st coordinate): analogous to the 0-th coordinate version, scaling $y$ by the same factor. -/
theorem stereo_fwd_bwd_1 (a b c x₀ y₀ z₀ x y z : K)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0)
    (honC : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) :
    stereoForward a b x₀ y₀ z₀ (x * z₀ - x₀ * z) (y * z₀ - y₀ * z) 1 =
    2 * z₀ ^ 2 * (a * x₀ * x + b * y₀ * y + c * z₀ * z) * y := by
  simp only [stereoForward]
  linear_combination (y₀ * z ^ 2 - 2 * y * z * z₀) * hpt - y₀ * z₀ ^ 2 * honC

/-- Composition identity (forward-then-backward, 2nd coordinate): scales $z$ by the same factor. -/
theorem stereo_fwd_bwd_2 (a b c x₀ y₀ z₀ x y z : K)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0)
    (honC : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) :
    stereoForward a b x₀ y₀ z₀ (x * z₀ - x₀ * z) (y * z₀ - y₀ * z) 2 =
    2 * z₀ ^ 2 * (a * x₀ * x + b * y₀ * y + c * z₀ * z) * z := by
  simp only [stereoForward]
  linear_combination -z₀ ^ 3 * honC - z₀ * z ^ 2 * hpt

/-- Quadratic homogeneity: scaling the input $(U, V)$ by $t$ scales the stereographic forward map by $t^2$ (so it descends to projective space). -/
theorem stereoForward_smul (a b x₀ y₀ z₀ t U V : K) (i : Fin 3) :
    stereoForward a b x₀ y₀ z₀ (t * U) (t * V) i =
    t ^ 2 * stereoForward a b x₀ y₀ z₀ U V i := by
  fin_cases i <;> simp only [stereoForward] <;> ring


/-- The bilinear pairing $\langle (x_0, y_0, z_0), (x, y, z) \rangle = a x_0 x + b y_0 y + c z_0 z$ associated to the diagonal conic; encodes the polarization of the quadratic form. -/
def bilinScalar (a b c x₀ y₀ z₀ x y z : K) : K :=
  a * x₀ * x + b * y₀ * y + c * z₀ * z


/-- Auxiliary: if both $au^2 + bv^2 = 0$ and a related polynomial vanish (with the standard nondegeneracy hypotheses), then $u = 0$. Used in `bilinScalar_zero_iff_proportional`. -/
lemma aux_u_eq_zero {a b c x₀ y₀ z₀ u v : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (h2ne : (2 : K) ≠ 0)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0)
    (h1 : a * u ^ 2 + b * v ^ 2 = 0)
    (h2 : a * x₀ * u ^ 2 + 2 * b * y₀ * u * v - b * x₀ * v ^ 2 = 0) :
    u = 0 := by
  have h2' : 2 * b * v * (y₀ * u - x₀ * v) = 0 := by linear_combination h2 - x₀ * h1
  have hbne : (2 : K) * b ≠ 0 := mul_ne_zero h2ne hb
  rcases mul_eq_zero.mp h2' with h2a | h2b
  · rcases mul_eq_zero.mp h2a with h2b_bad | hv
    · exact absurd h2b_bad hbne
    · subst hv
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        add_zero] at h1
      rcases mul_eq_zero.mp h1 with ha' | hu2
      · exact absurd ha' ha
      · exact pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp hu2
  · have key : u ^ 2 * (a * x₀ ^ 2 + b * y₀ ^ 2) = 0 := by
      have : u ^ 2 * (a * x₀ ^ 2 + b * y₀ ^ 2) =
        b * (y₀ * u - x₀ * v) * (y₀ * u + x₀ * v) +
        x₀ ^ 2 * (a * u ^ 2 + b * v ^ 2) := by ring
      rw [this, h2b, h1]; ring
    have hsum_ne : a * x₀ ^ 2 + b * y₀ ^ 2 ≠ 0 := by
      intro h
      have := hpt; rw [show a * x₀ ^ 2 + b * y₀ ^ 2 = 0 from h, zero_add] at this
      exact mul_ne_zero hc (pow_ne_zero _ hz₀) this
    rcases mul_eq_zero.mp key with hu2 | hsum
    · exact pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp hu2
    · exact absurd hsum hsum_ne

/-- Tangent line criterion: a nonzero point $(x, y, z)$ on the diagonal conic with $\langle p_0, p \rangle = 0$ (i.e., on the tangent line at $p_0$) must be proportional to $p_0 = (x_0, y_0, z_0)$. -/
theorem bilinScalar_zero_iff_proportional
    (a b c x₀ y₀ z₀ x y z : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (h2ne : (2 : K) ≠ 0)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0)
    (honC : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0)
    (hne : (x, y, z) ≠ (0, 0, 0))
    (hscalar : bilinScalar a b c x₀ y₀ z₀ x y z = 0) :
    ∃ t : K, x = t * x₀ ∧ y = t * y₀ ∧ z = t * z₀ := by
  unfold bilinScalar at hscalar
  by_cases hz : z = 0
  ·
    rw [hz] at honC hscalar ⊢
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero] at honC hscalar

    by_cases hy : y = 0
    · rw [hy] at honC hscalar ⊢
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        add_zero] at honC
      have hx : x = 0 := by
        rcases mul_eq_zero.mp honC with ha' | hx2
        · exact absurd ha' ha
        · exact pow_eq_zero_iff (by omega) |>.mp hx2
      exact absurd (by simp [hx, hy, hz] : (x, y, z) = (0, 0, 0)) hne
    ·
      exfalso
      have hkey : y ^ 2 * (a * x₀ ^ 2 + b * y₀ ^ 2) = 0 := by
        have hsq : (a * x₀ * x + b * y₀ * y) ^ 2 = 0 := by rw [hscalar]; ring
        have h1 : a ^ 2 * x₀ ^ 2 * x ^ 2 + 2 * a * b * x₀ * x * y₀ * y +
            b ^ 2 * y₀ ^ 2 * y ^ 2 = 0 := by linear_combination hsq
        have h2 : a * x₀ ^ 2 * (a * x ^ 2 + b * y ^ 2) = 0 := by rw [honC]; ring
        have h3 : b * (-a * x₀ ^ 2 * y ^ 2 + 2 * a * x₀ * x * y₀ * y +
            b * y₀ ^ 2 * y ^ 2) = 0 := by linear_combination h1 - h2
        have h5 : -a * x₀ ^ 2 * y ^ 2 + 2 * a * x₀ * x * y₀ * y +
            b * y₀ ^ 2 * y ^ 2 = 0 := by
          cases mul_eq_zero.mp h3 with
          | inl hb' => exact absurd hb' hb
          | inr h => exact h
        linear_combination -h5 + 2 * y₀ * y * hscalar
      cases mul_eq_zero.mp hkey with
      | inl hy2 => exact hy (pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp hy2)
      | inr hsum =>
        have : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = c * z₀ ^ 2 := by rw [hsum]; ring
        rw [this] at hpt
        exact mul_ne_zero hc (pow_ne_zero _ hz₀) hpt

  ·
    use z / z₀
    set u := x * z₀ - x₀ * z with hu_def
    set v := y * z₀ - y₀ * z with hv_def
    have h1 : a * u ^ 2 + b * v ^ 2 = 0 := by
      linear_combination z₀ ^ 2 * honC + z ^ 2 * hpt - 2 * z * z₀ * hscalar
    have h_comp0 : a * x₀ * u ^ 2 + 2 * b * y₀ * u * v - b * x₀ * v ^ 2 = 0 := by
      simp only [hu_def, hv_def]
      linear_combination
        (x₀ * z ^ 2 - 2 * x * z * z₀) * hpt - x₀ * z₀ ^ 2 * honC +
        2 * x * z₀ ^ 2 * hscalar
    have hu0 : u = 0 := aux_u_eq_zero ha hb hc hz₀ h2ne hpt h1 h_comp0
    have hv0 : v = 0 := by
      rw [hu0] at h1
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_add] at h1
      rcases mul_eq_zero.mp h1 with hb' | hv2
      · exact absurd hb' hb
      · exact pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp hv2
    have hxz₀ : x * z₀ = x₀ * z := sub_eq_zero.mp hu0
    have hyz₀ : y * z₀ = y₀ * z := sub_eq_zero.mp hv0
    exact ⟨by rw [div_mul_eq_mul_div, eq_div_iff hz₀]; linear_combination hxz₀,
           by rw [div_mul_eq_mul_div, eq_div_iff hz₀]; linear_combination hyz₀,
           by field_simp⟩

/-- Packaged isomorphism data for Theorem 2.3: the stereographic forward map lands on the conic, the back-then-forward and forward-then-backward maps are scalar multiples of the identity, and the tangent line through the base point intersects the conic only at the base point. Together these say the stereographic projection induces a bijection $\mathbb{P}^1 \cong $ conic. -/
theorem conic_P1_isomorphism (a b c x₀ y₀ z₀ : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (h2ne : (2 : K) ≠ 0)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0) :

    (∀ U V : K,
      a * (stereoForward a b x₀ y₀ z₀ U V 0) ^ 2 +
      b * (stereoForward a b x₀ y₀ z₀ U V 1) ^ 2 +
      c * (stereoForward a b x₀ y₀ z₀ U V 2) ^ 2 = 0) ∧

    (∀ U V : K, ∀ i : Fin 2,
      stereoBackward x₀ y₀ z₀ (stereoForward a b x₀ y₀ z₀ U V) i =
      2 * z₀ * (a * x₀ * U + b * y₀ * V) *
        (fun j : Fin 2 => match j with | 0 => U | 1 => V) i) ∧

    (∀ x y z : K,
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 →
      ∀ i : Fin 3,
        stereoForward a b x₀ y₀ z₀ (x * z₀ - x₀ * z) (y * z₀ - y₀ * z) i =
        2 * z₀ ^ 2 * (a * x₀ * x + b * y₀ * y + c * z₀ * z) *
          (fun j : Fin 3 => match j with | 0 => x | 1 => y | 2 => z) i) ∧


    (∀ x y z : K,
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 →
      (x, y, z) ≠ (0, 0, 0) →
      bilinScalar a b c x₀ y₀ z₀ x y z = 0 →
      ∃ t : K, x = t * x₀ ∧ y = t * y₀ ∧ z = t * z₀) := by
  refine ⟨fun U V => stereoForward_on_conic a b c x₀ y₀ z₀ U V hpt,
         fun U V i => ?_, fun x y z honC i => ?_,
         fun x y z honC hne hscalar =>
           bilinScalar_zero_iff_proportional a b c x₀ y₀ z₀ x y z
             ha hb hc hz₀ h2ne hpt honC hne hscalar⟩
  ·
    fin_cases i
    · exact stereo_bwd_fwd_0 a b x₀ y₀ z₀ U V
    · exact stereo_bwd_fwd_1 a b x₀ y₀ z₀ U V
  ·
    fin_cases i
    · exact stereo_fwd_bwd_0 a b c x₀ y₀ z₀ x y z hpt honC
    · exact stereo_fwd_bwd_1 a b c x₀ y₀ z₀ x y z hpt honC
    · exact stereo_fwd_bwd_2 a b c x₀ y₀ z₀ x y z hpt honC

/-- A function $v : \mathrm{Fin}\,2 \to K$ is nonzero iff not both coordinates $v(0), v(1)$ are zero. -/
lemma fin2_ne_zero_iff {K : Type*} [Field K] (v : Fin 2 → K) :
    v ≠ 0 ↔ ¬(v 0 = 0 ∧ v 1 = 0) := by
  constructor
  · intro hv ⟨h0, h1⟩; apply hv; ext i; fin_cases i <;> assumption
  · intro hv h; apply hv; exact ⟨by rw [h]; rfl, by rw [h]; rfl⟩


/-- The stereographic forward map sends any nonzero $(U, V)$ to a nonzero point of $K^3$. This is needed to descend the map to projective space. -/
theorem stereoForward_ne_zero (a b c x₀ y₀ z₀ U V : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (h2ne : (2 : K) ≠ 0)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0)
    (hUV : ¬(U = 0 ∧ V = 0)) :
    stereoForward a b x₀ y₀ z₀ U V ≠ 0 := by
  intro h
  have h0 : stereoForward a b x₀ y₀ z₀ U V 0 = 0 := by rw [h]; rfl
  have h2 : stereoForward a b x₀ y₀ z₀ U V 2 = 0 := by rw [h]; rfl
  simp only [stereoForward] at h0 h2
  have haUbV : a * U ^ 2 + b * V ^ 2 = 0 := by
    have : z₀ * (a * U ^ 2 + b * V ^ 2) = 0 := by linear_combination -h2
    exact (mul_eq_zero.mp this).resolve_left hz₀
  have key : 2 * b * V * (y₀ * U - x₀ * V) = 0 := by linear_combination h0 - x₀ * haUbV
  have h2bne : (2 : K) * b ≠ 0 := mul_ne_zero h2ne hb
  have hsum_ne : a * x₀ ^ 2 + b * y₀ ^ 2 ≠ 0 := by
    intro hsum
    have : c * z₀ ^ 2 = 0 := by linear_combination hpt - hsum
    exact mul_ne_zero hc (pow_ne_zero _ hz₀) this
  rcases mul_eq_zero.mp key with h2bV | hyx
  · rcases mul_eq_zero.mp h2bV with h2b_bad | hV
    · exact absurd h2b_bad h2bne
    · have hU : U = 0 := by
        have : a * U ^ 2 = 0 := by
          rw [hV, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] at haUbV; exact haUbV
        exact (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp ((mul_eq_zero.mp this).resolve_left ha)
      exact hUV ⟨hU, hV⟩
  · have hyx_eq : y₀ * U = x₀ * V := sub_eq_zero.mp hyx
    have hkey : U ^ 2 * (a * x₀ ^ 2 + b * y₀ ^ 2) = 0 := by
      have : U ^ 2 * (a * x₀ ^ 2 + b * y₀ ^ 2) =
        x₀ ^ 2 * (a * U ^ 2 + b * V ^ 2) +
          b * (y₀ * U - x₀ * V) * (y₀ * U + x₀ * V) := by ring
      rw [this, haUbV, show y₀ * U - x₀ * V = 0 from sub_eq_zero.mpr hyx_eq]; ring
    rcases mul_eq_zero.mp hkey with hU2 | hsum
    · have hU : U = 0 := (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp hU2
      have hV : V = 0 := by
        rw [hU, mul_zero] at hyx_eq
        rcases mul_eq_zero.mp hyx_eq.symm with hx | hV
        · have : b * V ^ 2 = 0 := by
            rw [hU, zero_pow (by omega : 2 ≠ 0), mul_zero, zero_add] at haUbV; exact haUbV
          exact (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp ((mul_eq_zero.mp this).resolve_left hb)
        · exact hV
      exact hUV ⟨hU, hV⟩
    · exact absurd hsum hsum_ne

/-- The diagonal conic as a subset of $\mathbb{P}^2(K)$: the projective points $[x : y : z]$ satisfying $ax^2 + by^2 + cz^2 = 0$. -/
def DiagConicSet (K : Type*) [Field K] (a b c : K) :
    Set (Projectivization K (Fin 3 → K)) :=
  { P | a * (P.rep 0) ^ 2 + b * (P.rep 1) ^ 2 + c * (P.rep 2) ^ 2 = 0 }

/-- The projectivized stereographic forward map $\mathbb{P}^1(K) \to \mathbb{P}^2(K)$ induced by `stereoForward`, using the quadratic homogeneity to descend to projective space. -/
noncomputable def stereoForwardProj (a b c x₀ y₀ z₀ : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0) (h2ne : (2 : K) ≠ 0)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0) :
    Projectivization K (Fin 2 → K) → Projectivization K (Fin 3 → K) :=
  Projectivization.lift
    (fun v => Projectivization.mk K
      (stereoForward a b x₀ y₀ z₀ (v.val 0) (v.val 1))
      (stereoForward_ne_zero a b c x₀ y₀ z₀ _ _ ha hb hc hz₀ h2ne hpt
        ((fin2_ne_zero_iff _).mp v.prop)))
    (by
      intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ t ht
      have hw : w₁ = t • w₂ := ht
      have h0 : w₁ 0 = t * w₂ 0 := by rw [hw]; simp [Pi.smul_apply, smul_eq_mul]
      have h1 : w₁ 1 = t * w₂ 1 := by rw [hw]; simp [Pi.smul_apply, smul_eq_mul]
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨t ^ 2, funext fun i => by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [h0, h1]
        exact (stereoForward_smul a b x₀ y₀ z₀ t (w₂ 0) (w₂ 1) i).symm⟩)


/-- The diagonal quadratic form $a X^2 + b Y^2 + c Z^2$ vanishes at the chosen representative of $[v] \in \mathbb{P}^2$ iff it vanishes at $v$ itself; this lets us pass between affine and projective conditions. -/
lemma diagQuad_rep_iff (a b c : K) (v : Fin 3 → K) (hv : v ≠ 0) :
    a * ((Projectivization.mk K v hv).rep 0) ^ 2 +
    b * ((Projectivization.mk K v hv).rep 1) ^ 2 +
    c * ((Projectivization.mk K v hv).rep 2) ^ 2 = 0 ↔
    a * (v 0) ^ 2 + b * (v 1) ^ 2 + c * (v 2) ^ 2 = 0 := by
  obtain ⟨t, ht⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  have hrep : ∀ i, (Projectivization.mk K v hv).rep i = (t : K) * v i := by
    intro i; exact (congr_fun ht i).symm
  rw [hrep 0, hrep 1, hrep 2]
  constructor
  · intro h
    have : (t : K) ^ 2 * (a * (v 0) ^ 2 + b * (v 1) ^ 2 + c * (v 2) ^ 2) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 (Units.ne_zero t))
  · intro h; linear_combination (↑t) ^ 2 * h

/-- The projectivized stereographic forward map lands on the diagonal conic: for every $Q \in \mathbb{P}^1$, the image $\varphi(Q)$ lies in `DiagConicSet`. -/
lemma stereoForwardProj_mem_conic (a b c x₀ y₀ z₀ : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0) (h2ne : (2 : K) ≠ 0)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0)
    (Q : Projectivization K (Fin 2 → K)) :
    stereoForwardProj a b c x₀ y₀ z₀ ha hb hc hz₀ h2ne hpt Q ∈ DiagConicSet K a b c := by
  induction Q using Projectivization.ind with
  | h v hv =>
    simp only [stereoForwardProj, DiagConicSet, Set.mem_setOf_eq, Projectivization.lift_mk]
    rw [diagQuad_rep_iff]
    exact stereoForward_on_conic a b c x₀ y₀ z₀ (v 0) (v 1) hpt

/-- Theorem 2.3 (bijective form): a smooth diagonal conic with a rational base point $(x_0, y_0, z_0)$ admits a bijection $\mathbb{P}^1(K) \to \mathrm{Conic}$ given by stereographic projection. -/
theorem conic_isomorphic_to_P1 (a b c x₀ y₀ z₀ : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (h2ne : (2 : K) ≠ 0)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0) :
    ∃ f : Projectivization K (Fin 2 → K) → DiagConicSet K a b c,
      Function.Bijective f := by

  let φ := stereoForwardProj a b c x₀ y₀ z₀ ha hb hc hz₀ h2ne hpt
  let f : Projectivization K (Fin 2 → K) → DiagConicSet K a b c :=
    fun Q => ⟨φ Q, stereoForwardProj_mem_conic a b c x₀ y₀ z₀ ha hb hc hz₀ h2ne hpt Q⟩
  refine ⟨f, ?_, ?_⟩
  ·
    intro Q₁ Q₂ hfQ

    have hφeq : φ Q₁ = φ Q₂ := congrArg Subtype.val hfQ

    induction Q₁ using Projectivization.ind with | h u hu =>
    induction Q₂ using Projectivization.ind with | h w hw =>


    simp only [φ, stereoForwardProj, Projectivization.lift_mk] at hφeq

    rw [Projectivization.mk_eq_mk_iff'] at hφeq ⊢
    obtain ⟨s, hs⟩ := hφeq


    set lu := 2 * z₀ * (a * x₀ * u 0 + b * y₀ * u 1) with hlu_def
    set lw := 2 * z₀ * (a * x₀ * w 0 + b * y₀ * w 1) with hlw_def

    have keq0 : lu * u 0 = s * lw * w 0 := by
      have h1 : stereoBackward x₀ y₀ z₀ (stereoForward a b x₀ y₀ z₀ (u 0) (u 1)) 0 =
          lu * u 0 := by simp only [stereoBackward, stereoForward, hlu_def]; ring
      have h2 : stereoBackward x₀ y₀ z₀ (fun j => s * stereoForward a b x₀ y₀ z₀ (w 0) (w 1) j) 0 =
          s * lw * w 0 := by simp only [stereoBackward, stereoForward, hlw_def]; ring
      have hfwd_eq : ∀ j, stereoForward a b x₀ y₀ z₀ (u 0) (u 1) j =
          s * stereoForward a b x₀ y₀ z₀ (w 0) (w 1) j := by
        intro j; have := congr_fun hs j
        simp only [Pi.smul_apply, smul_eq_mul] at this; exact this.symm
      rw [show stereoForward a b x₀ y₀ z₀ (u 0) (u 1) =
          (fun j => s * stereoForward a b x₀ y₀ z₀ (w 0) (w 1) j) from funext hfwd_eq] at h1
      rw [← h1, ← h2]
    have keq1 : lu * u 1 = s * lw * w 1 := by
      have h1 : stereoBackward x₀ y₀ z₀ (stereoForward a b x₀ y₀ z₀ (u 0) (u 1)) 1 =
          lu * u 1 := by simp only [stereoBackward, stereoForward, hlu_def]; ring
      have hfwd_eq : ∀ j, stereoForward a b x₀ y₀ z₀ (u 0) (u 1) j =
          s * stereoForward a b x₀ y₀ z₀ (w 0) (w 1) j := by
        intro j; have := congr_fun hs j
        simp only [Pi.smul_apply, smul_eq_mul] at this; exact this.symm
      have h2 : stereoBackward x₀ y₀ z₀ (fun j => s * stereoForward a b x₀ y₀ z₀ (w 0) (w 1) j) 1 =
          s * lw * w 1 := by simp only [stereoBackward, stereoForward, hlw_def]; ring
      rw [show stereoForward a b x₀ y₀ z₀ (u 0) (u 1) =
          (fun j => s * stereoForward a b x₀ y₀ z₀ (w 0) (w 1) j) from funext hfwd_eq] at h1
      rw [← h1, ← h2]

    by_cases hlw : lw = 0
    ·

      have hlu : lu = 0 := by
        by_contra hlu_ne
        have : u 0 = 0 := by
          have := keq0; rw [hlw, mul_zero, zero_mul] at this
          exact (mul_eq_zero.mp this).resolve_left hlu_ne
        have : u 1 = 0 := by
          have := keq1; rw [hlw, mul_zero, zero_mul] at this
          exact (mul_eq_zero.mp this).resolve_left hlu_ne
        exact hu (by ext i; fin_cases i <;> assumption)


      have hsum_ne : a * x₀ ^ 2 + b * y₀ ^ 2 ≠ 0 := by
        intro hsum
        have : c * z₀ ^ 2 = 0 := by linear_combination hpt - hsum
        exact mul_ne_zero hc (pow_ne_zero _ hz₀) this
      have hlu_eq : a * x₀ * u 0 + b * y₀ * u 1 = 0 := by
        have : 2 * z₀ * (a * x₀ * u 0 + b * y₀ * u 1) = 0 := hlu
        exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2ne hz₀)
      have hlw_eq : a * x₀ * w 0 + b * y₀ * w 1 = 0 := by
        have : 2 * z₀ * (a * x₀ * w 0 + b * y₀ * w 1) = 0 := hlw
        exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2ne hz₀)


      have hdet : u 0 * w 1 = u 1 * w 0 := by
        have h1 : a * x₀ * (u 0 * w 1 - u 1 * w 0) = 0 := by
          linear_combination w 1 * hlu_eq - u 1 * hlw_eq
        have h2 : b * y₀ * (u 0 * w 1 - u 1 * w 0) = 0 := by
          linear_combination u 0 * hlw_eq - w 0 * hlu_eq

        by_contra hdet_ne
        have hdet_ne' : u 0 * w 1 - u 1 * w 0 ≠ 0 := sub_ne_zero.mpr hdet_ne
        have hax₀ : a * x₀ = 0 := (mul_eq_zero.mp h1).resolve_right hdet_ne'
        have hby₀ : b * y₀ = 0 := (mul_eq_zero.mp h2).resolve_right hdet_ne'
        rcases mul_eq_zero.mp hax₀ with ha' | hx₀
        · exact ha ha'
        · rcases mul_eq_zero.mp hby₀ with hb' | hy₀
          · exact hb hb'
          · rw [hx₀, hy₀] at hsum_ne
            simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
              add_zero, not_true] at hsum_ne


      have : ¬(w 0 = 0 ∧ w 1 = 0) := (fin2_ne_zero_iff w).mp hw
      rcases not_and_or.mp this with hw0 | hw1
      · use u 0 / w 0
        ext i; fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul]
        · exact div_mul_cancel₀ (u 0) hw0
        · show u 0 / w 0 * w 1 = u 1
          field_simp
          linear_combination hdet
      · use u 1 / w 1
        ext i; fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul]
        · show u 1 / w 1 * w 0 = u 0
          field_simp
          linear_combination -hdet
        · exact div_mul_cancel₀ (u 1) hw1
    ·


      by_cases hlu : lu = 0
      · exfalso
        have : s * lw = 0 := by
          have : ¬(w 0 = 0 ∧ w 1 = 0) := (fin2_ne_zero_iff w).mp hw
          rcases not_and_or.mp this with hw0 | hw1
          · exact (mul_eq_zero.mp (by rw [hlu, zero_mul] at keq0; exact keq0.symm)).resolve_right hw0
          · exact (mul_eq_zero.mp (by rw [hlu, zero_mul] at keq1; exact keq1.symm)).resolve_right hw1
        have hs0 : s = 0 := (mul_eq_zero.mp this).resolve_right hlw

        have : stereoForward a b x₀ y₀ z₀ (u 0) (u 1) = 0 := by
          ext j; have := congr_fun hs j
          simp only [Pi.smul_apply, smul_eq_mul] at this
          simp only [Pi.zero_apply]
          rw [hs0, zero_mul] at this; exact this.symm
        exact stereoForward_ne_zero a b c x₀ y₀ z₀ _ _ ha hb hc hz₀ h2ne hpt
          ((fin2_ne_zero_iff _).mp hu) this
      ·
        use s * lw / lu
        ext i; fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul]
        · show s * lw / lu * w 0 = u 0
          have h := keq0.symm
          rw [show s * lw / lu * w 0 = s * lw * w 0 * lu⁻¹ from by ring, h,
              show lu * u 0 * lu⁻¹ = u 0 * (lu * lu⁻¹) from by ring,
              mul_inv_cancel₀ hlu, mul_one]
        · show s * lw / lu * w 1 = u 1
          have h := keq1.symm
          rw [show s * lw / lu * w 1 = s * lw * w 1 * lu⁻¹ from by ring, h,
              show lu * u 1 * lu⁻¹ = u 1 * (lu * lu⁻¹) from by ring,
              mul_inv_cancel₀ hlu, mul_one]
  ·
    intro ⟨P, hP⟩

    induction P using Projectivization.ind with | h v hv =>


    simp only [DiagConicSet, Set.mem_setOf_eq] at hP
    have honC : a * (v 0) ^ 2 + b * (v 1) ^ 2 + c * (v 2) ^ 2 = 0 :=
      (diagQuad_rep_iff a b c v hv).mp hP

    set U := v 0 * z₀ - x₀ * v 2 with hU_def
    set V := v 1 * z₀ - y₀ * v 2 with hV_def


    by_cases hUV : U = 0 ∧ V = 0
    ·


      obtain ⟨hU0, hV0⟩ := hUV


      have hbya : ¬(b * y₀ = 0 ∧ -(a * x₀) = 0) := by
        intro ⟨hby, hax⟩
        have hax' : a * x₀ = 0 := neg_eq_zero.mp hax
        rcases mul_eq_zero.mp hby with hb' | hy₀
        · exact hb hb'
        · rcases mul_eq_zero.mp hax' with ha' | hx₀
          · exact ha ha'
          · have : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = c * z₀ ^ 2 := by
              rw [hx₀, hy₀]; ring
            rw [this] at hpt
            exact mul_ne_zero hc (pow_ne_zero _ hz₀) hpt

      let w : Fin 2 → K := fun i => match i with | 0 => b * y₀ | 1 => -(a * x₀)
      have hw : w ≠ 0 := (fin2_ne_zero_iff w).mpr hbya
      refine ⟨Projectivization.mk K w hw, ?_⟩

      apply Subtype.ext
      simp only [f, φ, stereoForwardProj, Projectivization.lift_mk, w]

      rw [Projectivization.mk_eq_mk_iff']

      have sfwd0 : stereoForward a b x₀ y₀ z₀ (b * y₀) (-(a * x₀)) 0 =
          a * b * c * z₀ ^ 2 * x₀ := by
        simp only [stereoForward]; linear_combination -(a * b * x₀) * hpt
      have sfwd1 : stereoForward a b x₀ y₀ z₀ (b * y₀) (-(a * x₀)) 1 =
          a * b * c * z₀ ^ 2 * y₀ := by
        simp only [stereoForward]; linear_combination -(a * b * y₀) * hpt
      have sfwd2 : stereoForward a b x₀ y₀ z₀ (b * y₀) (-(a * x₀)) 2 =
          a * b * c * z₀ ^ 2 * z₀ := by
        simp only [stereoForward]; linear_combination -(a * b * z₀) * hpt

      have hv0 : v 0 * z₀ = x₀ * v 2 := by linear_combination hU0
      have hv1 : v 1 * z₀ = y₀ * v 2 := by linear_combination hV0

      have hv2 : v 2 ≠ 0 := by
        intro hv2; apply hv; ext j; fin_cases j
        · have := hv0; rw [hv2, mul_zero] at this
          exact (mul_eq_zero.mp this).resolve_right hz₀
        · have := hv1; rw [hv2, mul_zero] at this
          exact (mul_eq_zero.mp this).resolve_right hz₀
        · exact hv2

      use a * b * c * z₀ ^ 3 / v 2
      have hvi0 : v 0 = x₀ * v 2 / z₀ := by rw [eq_div_iff hz₀]; linear_combination hv0
      have hvi1 : v 1 = y₀ * v 2 / z₀ := by rw [eq_div_iff hz₀]; linear_combination hv1
      ext i; simp only [Pi.smul_apply, smul_eq_mul]
      fin_cases i
      · show a * b * c * z₀ ^ 3 / v 2 * v 0 =
            stereoForward a b x₀ y₀ z₀ (b * y₀) (-(a * x₀)) 0
        rw [sfwd0, hvi0]; field_simp
      · show a * b * c * z₀ ^ 3 / v 2 * v 1 =
            stereoForward a b x₀ y₀ z₀ (b * y₀) (-(a * x₀)) 1
        rw [sfwd1, hvi1]; field_simp
      · show a * b * c * z₀ ^ 3 / v 2 * v 2 =
            stereoForward a b x₀ y₀ z₀ (b * y₀) (-(a * x₀)) 2
        rw [sfwd2]; field_simp
    ·


      have hUV' : ¬(U = 0 ∧ V = 0) := hUV
      let w : Fin 2 → K := fun i => match i with | 0 => U | 1 => V
      have hw : w ≠ 0 := (fin2_ne_zero_iff w).mpr hUV'
      refine ⟨Projectivization.mk K w hw, ?_⟩
      apply Subtype.ext
      simp only [f, φ, stereoForwardProj, Projectivization.lift_mk, w]
      rw [Projectivization.mk_eq_mk_iff']


      set scalar := 2 * z₀ ^ 2 * (a * x₀ * v 0 + b * y₀ * v 1 + c * z₀ * v 2)
      use scalar
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      fin_cases i
      ·
        show scalar * v 0 = stereoForward a b x₀ y₀ z₀ U V 0
        rw [hU_def, hV_def]
        have := stereo_fwd_bwd_0 a b c x₀ y₀ z₀ (v 0) (v 1) (v 2) hpt honC
        exact this.symm
      ·
        show scalar * v 1 = stereoForward a b x₀ y₀ z₀ U V 1
        rw [hU_def, hV_def]
        have := stereo_fwd_bwd_1 a b c x₀ y₀ z₀ (v 0) (v 1) (v 2) hpt honC
        exact this.symm
      ·
        show scalar * v 2 = stereoForward a b x₀ y₀ z₀ U V 2
        rw [hU_def, hV_def]
        have := stereo_fwd_bwd_2 a b c x₀ y₀ z₀ (v 0) (v 1) (v 2) hpt honC
        exact this.symm

/-- Theorem 2.3 (equivalence form): the diagonal conic variety with a rational base point is in bijection with $\mathbb{P}^1$ — packaged as an `Equiv` (the bijection from `conic_isomorphic_to_P1` upgraded to an isomorphism of sets). -/
theorem conic_variety_isomorphic_to_P1 (a b c x₀ y₀ z₀ : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (h2ne : (2 : K) ≠ 0)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0) :


    Nonempty (↥(DiagConicSet K a b c) ≃ Projectivization K (Fin 2 → K)) := by

  obtain ⟨g, hg⟩ := conic_isomorphic_to_P1 a b c x₀ y₀ z₀ ha hb hc hz₀ h2ne hpt
  exact ⟨(Equiv.ofBijective g hg).symm⟩

end Theorem23

end
