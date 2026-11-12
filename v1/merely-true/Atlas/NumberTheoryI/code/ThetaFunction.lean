/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds

open Complex Filter Asymptotics Function Set
open scoped Real Topology

noncomputable section

lemma periodic_strip_to_global (f : ℂ → ℂ) (hf_per : Periodic f (1 : ℂ))
    (C : ℝ) (hC : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → ‖f s‖ ≤ C * Real.exp |s.im|) :
    ∀ s : ℂ, ‖f s‖ ≤ C * Real.exp |s.im| := by
  intro s
  set n := ⌊s.re⌋
  have hsub : f s = f (s - ↑n) := by
    have h := hf_per.int_mul (-n) s
    simp only [mul_one, Int.cast_neg] at h
    rw [show s + -↑n = s - ↑n from by ring] at h
    exact h.symm
  rw [hsub]
  have him : (s - ↑n).im = s.im := by simp
  have hre_lo : 0 ≤ (s - ↑n).re := by simp; linarith [Int.floor_le s.re]
  have hre_hi : (s - ↑n).re ≤ 1 := by simp; linarith [Int.lt_floor_add_one s.re]
  calc ‖f (s - ↑n)‖ ≤ C * Real.exp |(s - ↑n).im| := hC _ hre_lo hre_hi
    _ = C * Real.exp |s.im| := by rw [him]

lemma sin_pi_mul_add_one (z : ℂ) :
    Complex.sin (↑Real.pi * (z + 1)) = -Complex.sin (↑Real.pi * z) := by
  have : ↑Real.pi * (z + 1) = ↑Real.pi * z + ↑Real.pi := by ring
  rw [this, sin_add]
  have h1 : Complex.sin ↑Real.pi = 0 := by rw [← ofReal_sin, Real.sin_pi, ofReal_zero]
  have h2 : Complex.cos ↑Real.pi = -1 := by
    rw [← ofReal_cos, Real.cos_pi, ofReal_neg, ofReal_one]
  rw [h1, h2]; ring

lemma dense_sin_pi_ne_zero : Dense {z : ℂ | Complex.sin (↑Real.pi * z) ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU ⟨z₀, hz₀⟩
  by_contra h; push Not at h
  rw [eq_empty_iff_forall_notMem] at h
  have hall : ∀ z ∈ U, Complex.sin (↑Real.pi * z) = 0 := by
    intro z hz; by_contra hne; exact h z ⟨hz, hne⟩
  have hsin_an : AnalyticOnNhd ℂ (fun z => Complex.sin (↑Real.pi * z)) univ :=
    fun z _ => Complex.analyticAt_sin.comp (analyticAt_const.mul analyticAt_id)
  have hev : (fun z => Complex.sin (↑Real.pi * z)) =ᶠ[𝓝 z₀] 0 :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hz₀, fun z hz => hall z hz⟩
  have h1 : Complex.sin (↑Real.pi * (1/2 : ℂ)) = 0 :=
    (hsin_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z₀) hev) (mem_univ _)
  have h2 : ↑Real.pi * (1/2 : ℂ) = ↑(Real.pi / 2) := by push_cast; ring
  rw [h2, ← ofReal_sin, Real.sin_pi_div_two] at h1
  exact one_ne_zero (ofReal_eq_zero.mp h1)

lemma sin_pi_half_ne_zero : Complex.sin (↑Real.pi * (1/2 : ℂ)) ≠ 0 := by
  have : ↑Real.pi * (1/2 : ℂ) = ↑(Real.pi / 2) := by push_cast; ring
  rw [this, ← ofReal_sin, Real.sin_pi_div_two]
  exact ofReal_ne_zero.mpr one_ne_zero

lemma int_of_norm_sub_lt_one {k n : ℤ} (h : ‖(↑k : ℂ) - ↑n‖ < 1) : k = n := by
  have h1 : (↑(k - n) : ℂ) = (↑k : ℂ) - ↑n := by push_cast; ring
  rw [← h1, Complex.norm_intCast,
    show ((k - n : ℤ) : ℝ) = (k : ℝ) - n from by push_cast; ring, abs_sub_lt_iff] at h
  have h2 : k < n + 1 := by exact_mod_cast (show (k : ℝ) < n + 1 by linarith [h.1])
  have h3 : n < k + 1 := by exact_mod_cast (show (n : ℝ) < k + 1 by linarith [h.2])
  omega

lemma sin_pi_ne_zero_in_ball (n : ℤ) (z : ℂ)
    (hz : z ∈ Metric.ball (↑n : ℂ) 1) (hzn : z ≠ ↑n) :
    Complex.sin ((↑Real.pi : ℂ) * z) ≠ 0 := by
  intro h0; rw [sin_eq_zero_iff] at h0; obtain ⟨k, hk⟩ := h0
  have hzk : z = ↑k := by
    have : z * ↑Real.pi = ↑k * ↑Real.pi := by linear_combination hk
    exact mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) this
  exact hzn (hzk ▸ congr_arg _ (int_of_norm_sub_lt_one
    (by rw [← hzk, ← Complex.dist_eq]; exact Metric.mem_ball.mp hz)))

lemma dslope_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (dslope f c) := by
  rw [← differentiableOn_univ]
  exact (differentiableOn_dslope (isOpen_univ.mem_nhds (mem_univ c))).mpr hf.differentiableOn

lemma dslope_sinpi_at_int_ne_zero (n : ℤ) :
    dslope (fun z => Complex.sin ((↑Real.pi : ℂ) * z)) (↑n) (↑n) ≠ 0 := by
  rw [dslope_same]
  have hd : HasDerivAt (fun w => Complex.sin ((↑Real.pi : ℂ) * w))
      ((↑Real.pi : ℂ) * Complex.cos ((↑Real.pi : ℂ) * ↑n)) ↑n := by
    have : HasDerivAt (fun w => (↑Real.pi : ℂ) * w) (↑Real.pi : ℂ) (↑n : ℂ) := by
      simpa using (hasDerivAt_id (↑n : ℂ)).const_mul (↑Real.pi : ℂ)
    exact this.csin.congr_deriv (by ring)
  rw [hd.deriv]
  apply mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [mul_comm, ← ofReal_intCast, ← ofReal_mul, ← ofReal_cos, ofReal_ne_zero,
    Real.cos_int_mul_pi]
  exact zpow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)

lemma sinpi_differentiable :
    Differentiable ℂ (fun z => Complex.sin ((↑Real.pi : ℂ) * z)) :=
  Complex.differentiable_sin.comp (differentiable_const _ |>.mul differentiable_id)

noncomputable def mkQuotient (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  if Complex.sin ((↑Real.pi : ℂ) * z) = 0 then
    dslope h ↑(⌊z.re⌋ : ℤ) z /
      dslope (fun w => Complex.sin ((↑Real.pi : ℂ) * w)) ↑(⌊z.re⌋ : ℤ) z
  else h z / Complex.sin ((↑Real.pi : ℂ) * z)

theorem entire_quotient_by_sin_pi
    (h : ℂ → ℂ) (hh_diff : Differentiable ℂ h) (hh_zero : ∀ n : ℤ, h n = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      (∀ z, Complex.sin (↑Real.pi * z) ≠ 0 →
        g z = h z / Complex.sin (↑Real.pi * z)) := by
  refine ⟨mkQuotient h, ?_, fun z hz => by simp [mkQuotient, hz]⟩
  intro z₀
  by_cases hint : ∃ n : ℤ, z₀ = ↑n
  ·
    obtain ⟨n, rfl⟩ := hint
    have hdiff_ratio : DifferentiableAt ℂ
        (fun z => dslope h ↑n z /
          dslope (fun w => Complex.sin ((↑Real.pi : ℂ) * w)) ↑n z) ↑n :=
      (dslope_entire hh_diff n).differentiableAt.div
        (dslope_entire sinpi_differentiable n).differentiableAt
        (dslope_sinpi_at_int_ne_zero n)
    apply hdiff_ratio.congr_of_eventuallyEq
    apply Filter.eventually_of_mem (Metric.ball_mem_nhds (↑n : ℂ) one_pos)
    intro z hz
    show mkQuotient h z = dslope h ↑n z /
      dslope (fun w => Complex.sin ((↑Real.pi : ℂ) * w)) ↑n z
    by_cases hzn : z = ↑n
    · subst hzn; simp only [mkQuotient]
      rw [if_pos (by rw [sin_eq_zero_iff]; exact ⟨n, by ring⟩)]

      congr 1 <;> simp [Complex.intCast_re, Int.floor_intCast]
    · have hsin_ne := sin_pi_ne_zero_in_ball n z hz hzn
      simp only [mkQuotient, if_neg hsin_ne]
      have h1 : h z = (z - ↑n) * dslope h (↑n) z := by
        have := sub_smul_dslope h (↑n : ℂ) z
        simp only [smul_eq_mul] at this; rw [hh_zero n, sub_zero] at this; exact this.symm
      have h2 : Complex.sin ((↑Real.pi : ℂ) * z) =
          (z - ↑n) * dslope (fun w => Complex.sin ((↑Real.pi : ℂ) * w)) (↑n) z := by
        have := sub_smul_dslope (fun w => Complex.sin ((↑Real.pi : ℂ) * w)) (↑n : ℂ) z
        simp only [smul_eq_mul] at this
        have hsin0 : Complex.sin ((↑Real.pi : ℂ) * ↑n) = 0 := by
          rw [Complex.sin_eq_zero_iff]; exact ⟨n, by ring⟩
        rw [hsin0, sub_zero] at this; exact this.symm
      rw [h1, h2]
      exact (IsUnit.mk0 _ (sub_ne_zero.mpr hzn)).mul_div_mul_left _ _
  ·
    push Not at hint
    have hsin_ne : Complex.sin ((↑Real.pi : ℂ) * z₀) ≠ 0 := by
      intro h0; rw [Complex.sin_eq_zero_iff] at h0; obtain ⟨k, hk⟩ := h0
      exact hint k (mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero)
        (by linear_combination hk : z₀ * ↑Real.pi = ↑k * ↑Real.pi))
    have hdiff : DifferentiableAt ℂ (fun z => h z / Complex.sin ((↑Real.pi : ℂ) * z)) z₀ :=
      hh_diff.differentiableAt.div sinpi_differentiable.differentiableAt hsin_ne
    apply hdiff.congr_of_eventuallyEq
    apply (sinpi_differentiable.continuous.continuousAt.eventually_ne hsin_ne).mono
    intro z hz; simp [mkQuotient, hz]

lemma normSq_sin (z : ℂ) : Complex.normSq (Complex.sin z) =
    Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sin_eq z, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← ofReal_mul, ← ofReal_mul]
  simp only [normSq_apply, add_re, ofReal_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_zero,
    add_im, ofReal_im, mul_im, add_zero]
  nlinarith [Real.sin_sq_add_cos_sq z.re, Real.cosh_sq z.im]

lemma norm_sin_ge_abs_sinh_im (z : ℂ) : ‖Complex.sin z‖ ≥ |Real.sinh z.im| := by
  nlinarith [Complex.sq_norm (Complex.sin z), normSq_sin z, sq_nonneg (Real.sin z.re),
    sq_abs (Real.sinh z.im), norm_nonneg (Complex.sin z),
    sq_nonneg (‖Complex.sin z‖ - |Real.sinh z.im|)]

lemma sinh_ge_exp_div_four {t : ℝ} (ht : 1 ≤ t) : Real.sinh t ≥ Real.exp t / 4 := by
  rw [Real.sinh_eq]
  linarith [Real.add_one_le_exp t, Real.exp_le_one_iff.mpr (by linarith : -t ≤ 0)]

lemma norm_sin_pi_lower_bound (z : ℂ) (him : 1 ≤ |z.im|) :
    ‖Complex.sin (↑Real.pi * z)‖ ≥ Real.exp (Real.pi * |z.im|) / 4 := by
  have him_eq : (↑Real.pi * z).im = Real.pi * z.im := by
    simp [mul_im, ofReal_re, ofReal_im]
  calc ‖Complex.sin (↑Real.pi * z)‖
      ≥ |Real.sinh (↑Real.pi * z).im| := norm_sin_ge_abs_sinh_im _
    _ = |Real.sinh (Real.pi * z.im)| := by rw [him_eq]
    _ = Real.sinh |Real.pi * z.im| := Real.abs_sinh _
    _ = Real.sinh (Real.pi * |z.im|) := by rw [abs_mul, abs_of_pos Real.pi_pos]
    _ ≥ Real.exp (Real.pi * |z.im|) / 4 :=
        sinh_ge_exp_div_four (by nlinarith [Real.pi_gt_three])

lemma strip_box_compact : IsCompact {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · refine (isClosed_le continuous_const Complex.continuous_re).inter ?_
    exact (isClosed_le Complex.continuous_re continuous_const).inter
      (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
  · rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
    refine ⟨2, fun z hz => ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    obtain ⟨h1, h2, h3⟩ := hz
    nlinarith [Complex.sq_norm z, norm_nonneg z, sq_nonneg (‖z‖ - 2),
      abs_mul_abs_self z.im, abs_nonneg z.im, Complex.normSq_apply z]

theorem quotient_bounded_on_strip
    (h : ℂ → ℂ) (hh_diff : Differentiable ℂ h) (hh_zero : ∀ n : ℤ, h n = 0)
    (C : ℝ) (hC : ∀ s : ℂ, ‖h s‖ ≤ C * Real.exp |s.im|)
    (g : ℂ → ℂ) (hg_diff : Differentiable ℂ g)
    (hg_eq : ∀ z, Complex.sin (↑Real.pi * z) ≠ 0 →
        g z = h z / Complex.sin (↑Real.pi * z)) :
    ∃ M : ℝ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → ‖g s‖ ≤ M := by
  have hg_cont : Continuous g := hg_diff.continuous
  have hC_nn : 0 ≤ C := by
    have := hC 0; simp at this; linarith [norm_nonneg (h 0)]

  set K := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ 1}
  have hK_ne : K.Nonempty := ⟨0, by simp [K, abs_of_nonneg]⟩
  obtain ⟨z₀, _, hz₀_max⟩ := strip_box_compact.exists_isMaxOn hK_ne hg_cont.norm.continuousOn
  set M₁ := ‖g z₀‖

  have h_tail : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ |z.im| → ‖g z‖ ≤ 4 * C := by
    intro z hre0 hre1 him
    have hsin_ne : Complex.sin (↑Real.pi * z) ≠ 0 := by
      intro habs
      rw [Complex.sin_eq_zero_iff] at habs
      obtain ⟨k, hk⟩ := habs
      have hz_eq : z = (k : ℂ) := by
        have : (↑Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
        field_simp at hk; exact hk
      have : z.im = 0 := by rw [hz_eq]; simp
      rw [this] at him; simp at him; linarith
    rw [hg_eq z hsin_ne, norm_div]
    have h_den := norm_sin_pi_lower_bound z him
    have h_den_pos : ‖Complex.sin (↑Real.pi * z)‖ > 0 := norm_pos_iff.mpr hsin_ne
    rw [div_le_iff₀ h_den_pos]
    calc ‖h z‖ ≤ C * Real.exp |z.im| := hC z
      _ ≤ C * Real.exp (Real.pi * |z.im|) := by
          apply mul_le_mul_of_nonneg_left _ hC_nn
          exact Real.exp_le_exp_of_le (by nlinarith [Real.pi_gt_three, abs_nonneg z.im])
      _ ≤ 4 * C * ‖Complex.sin (↑Real.pi * z)‖ := by nlinarith

  exact ⟨max M₁ (4 * C), fun s hs0 hs1 => by
    by_cases him : |s.im| ≤ 1
    · calc ‖g s‖ ≤ M₁ := hz₀_max ⟨hs0, hs1, him⟩
        _ ≤ max M₁ (4 * C) := le_max_left _ _
    · push Not at him
      calc ‖g s‖ ≤ 4 * C := h_tail s hs0 hs1 him.le
        _ ≤ max M₁ (4 * C) := le_max_right _ _⟩

theorem entire_bounded_auxiliary
    (f : ℂ → ℂ) (hf_diff : Differentiable ℂ f) (hf_per : Periodic f (1 : ℂ))
    (C : ℝ) (hC_global : ∀ s : ℂ, ‖f s‖ ≤ C * Real.exp |s.im|) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      (∀ z, Complex.sin (↑Real.pi * z) ≠ 0 →
        g z = (f z - f 0) / Complex.sin (↑Real.pi * z)) ∧
      Bornology.IsBounded (range g) := by

  set h := fun z => f z - f 0 with hh_def
  have hh_diff : Differentiable ℂ h := hf_diff.sub (differentiable_const _)
  have hh_per : Periodic h (1 : ℂ) := by intro z; simp only [hh_def]; rw [hf_per z]
  have hh_zero : ∀ n : ℤ, h ↑n = 0 := by
    intro n; simp only [hh_def, sub_eq_zero]
    have := hf_per.int_mul n 0; simp at this; exact this

  have hh_bound : ∀ s : ℂ, ‖h s‖ ≤ (C + ‖f 0‖) * Real.exp |s.im| := by
    intro s
    calc ‖h s‖ = ‖f s - f 0‖ := rfl
      _ ≤ ‖f s‖ + ‖f 0‖ := norm_sub_le _ _
      _ ≤ C * Real.exp |s.im| + ‖f 0‖ := by linarith [hC_global s]
      _ ≤ C * Real.exp |s.im| + ‖f 0‖ * Real.exp |s.im| := by
          linarith [mul_le_mul_of_nonneg_left (Real.one_le_exp (abs_nonneg s.im))
            (norm_nonneg (f 0))]
      _ = (C + ‖f 0‖) * Real.exp |s.im| := by ring

  obtain ⟨g, hg_diff, hg_eq⟩ := entire_quotient_by_sin_pi h hh_diff hh_zero
  refine ⟨g, hg_diff, hg_eq, ?_⟩

  obtain ⟨M, hM⟩ := quotient_bounded_on_strip h hh_diff hh_zero (C + ‖f 0‖) hh_bound
    g hg_diff hg_eq


  have hanti : ∀ z, g (z + 1) = -g z := by
    intro z
    have hlhs : Continuous (fun z => g (z + 1)) :=
      hg_diff.continuous.comp (continuous_id.add continuous_const)
    have hrhs : Continuous (fun z => -g z) := hg_diff.continuous.neg
    suffices closure {z : ℂ | Complex.sin (↑Real.pi * z) ≠ 0} ⊆
        {z | g (z + 1) = -g z} by
      exact this (dense_sin_pi_ne_zero.closure_eq ▸ mem_univ z)
    apply closure_minimal
    · intro w hw
      simp only [mem_setOf_eq] at hw ⊢
      have hw1 : Complex.sin (↑Real.pi * (w + 1)) ≠ 0 := by
        rw [sin_pi_mul_add_one]; exact neg_ne_zero.mpr hw
      rw [hg_eq (w + 1) hw1, hg_eq w hw, hh_per w, sin_pi_mul_add_one]
      field_simp
    · exact isClosed_eq hlhs hrhs

  have hper2 : Periodic g (2 : ℂ) := by
    intro z; show g (z + 2) = g z
    have : g (z + 2) = g ((z + 1) + 1) := by congr 1; ring
    rw [this, hanti, hanti, neg_neg]

  have hM2 : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 → ‖g s‖ ≤ M := by
    intro s hs0 hs2
    by_cases hle : s.re ≤ 1
    · exact hM s hs0 hle
    · push Not at hle
      have hsub : g s = g ((s - 1) + 1) := by congr 1; ring
      rw [hsub, hanti, norm_neg]
      exact hM (s - 1) (by simp only [sub_re, one_re]; linarith)
        (by simp only [sub_re, one_re]; linarith)

  have hMg : ∀ s : ℂ, ‖g s‖ ≤ M := by
    intro s
    set n := ⌊s.re / 2⌋
    have hgt : g s = g (s - ↑(2 * n)) := by
      have hp := hper2.int_mul (-n) s
      simp only [Int.cast_neg] at hp
      rw [← hp]; congr 1; push_cast; ring
    rw [hgt]
    apply hM2
    · simp only [sub_re, intCast_re]; push_cast
      linarith [mul_le_mul_of_nonneg_left (Int.floor_le (s.re / 2)) (by norm_num : (0:ℝ) ≤ 2)]
    · simp only [sub_re, intCast_re]; push_cast
      linarith [mul_lt_mul_of_pos_left (Int.lt_floor_add_one (s.re / 2))
        (by norm_num : (0:ℝ) < 2)]

  rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
  exact ⟨M, fun x hx => by
    obtain ⟨z, rfl⟩ := hx
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hMg z⟩

lemma entire_periodic_exp_growth_bounded
    (f : ℂ → ℂ) (hf_diff : Differentiable ℂ f)
    (hf_per : Periodic f (1 : ℂ))
    (C : ℝ) (hC : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → ‖f s‖ ≤ C * Real.exp |s.im|) :
    Bornology.IsBounded (range f) := by

  have hC_global := periodic_strip_to_global f hf_per C hC

  obtain ⟨g, hg_diff, hg_eq, hg_bdd⟩ := entire_bounded_auxiliary f hf_diff hf_per C hC_global

  have ⟨c, hc⟩ : ∃ c, ∀ z, g z = c :=
    ⟨g 0, fun z => hg_diff.apply_eq_apply_of_bounded hg_bdd z 0⟩

  have hagree : ∀ z, Complex.sin (↑Real.pi * z) ≠ 0 →
      f z - f 0 = c * Complex.sin (↑Real.pi * z) := by
    intro z hz
    have h := hg_eq z hz; rw [hc z] at h
    rw [h, div_mul_cancel₀ _ hz]

  have hkey : ∀ z, f z - f 0 = c * Complex.sin (↑Real.pi * z) := by
    intro z
    have hlhs : Continuous (fun z => f z - f 0) := hf_diff.continuous.sub continuous_const
    have hrhs : Continuous (fun z => c * Complex.sin (↑Real.pi * z)) :=
      continuous_const.mul (Complex.continuous_sin.comp (continuous_const.mul continuous_id))
    have hclosed := isClosed_eq hlhs hrhs
    have hsub : {z | Complex.sin (↑Real.pi * z) ≠ 0} ⊆
        {z | f z - f 0 = c * Complex.sin (↑Real.pi * z)} := hagree
    exact eq_univ_iff_forall.mp
      (hclosed.closure_eq ▸ (dense_sin_pi_ne_zero.mono hsub).closure_eq) z

  have hc_zero : c = 0 := by
    have h1 := hkey (1/2 : ℂ)
    have h2 := hkey ((1/2 : ℂ) + 1)
    rw [show f ((1/2 : ℂ) + 1) = f (1/2 : ℂ) from hf_per (1/2), sin_pi_mul_add_one] at h2


    have heq : c * Complex.sin (↑Real.pi * (1/2 : ℂ)) =
               c * (-Complex.sin (↑Real.pi * (1/2 : ℂ))) := h1.symm.trans h2
    have h3 : c * (Complex.sin (↑Real.pi * (1/2 : ℂ)) -
               (-Complex.sin (↑Real.pi * (1/2 : ℂ)))) = 0 := by
      rw [mul_sub]; linear_combination heq
    have h4 : c * (2 * Complex.sin (↑Real.pi * (1/2 : ℂ))) = 0 := by
      convert h3 using 2; ring
    rw [mul_comm c, mul_assoc, mul_eq_zero, mul_eq_zero] at h4
    rcases h4 with h | h | h
    · exact absurd h two_ne_zero
    · exact absurd h sin_pi_half_ne_zero
    · exact h

  have hf_const : ∀ z, f z = f 0 := fun z =>
    sub_eq_zero.mp (by rw [hkey z, hc_zero, zero_mul])
  exact Bornology.isBounded_singleton.subset (by
    intro x hx; obtain ⟨z, hz⟩ := hx
    rw [mem_singleton_iff, ← hz]; exact hf_const z)

theorem periodic_entire_exp_growth_is_const
    (f : ℂ → ℂ)
    (hf_diff : Differentiable ℂ f)
    (hf_per : Periodic f (1 : ℂ))
    (hf_growth : ∃ C : ℝ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 →
      ‖f s‖ ≤ C * Real.exp |s.im|) :
    ∃ c : ℂ, f = Function.const ℂ c := by
  obtain ⟨C, hC⟩ := hf_growth
  have hbdd := entire_periodic_exp_growth_bounded f hf_diff hf_per C hC
  exact hf_diff.exists_eq_const_of_bounded hbdd

end
