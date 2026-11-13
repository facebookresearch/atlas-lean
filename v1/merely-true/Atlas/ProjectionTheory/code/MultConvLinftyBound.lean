/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.HighFreqMultConv
import Atlas.ProjectionTheory.code.BKTLemma2
import Atlas.ProjectionTheory.code.BKTLemma3
import Atlas.ProjectionTheory.code.MultConvProjection

open Finset Complex BigOperators

noncomputable section

namespace HighFreqMultConv

variable (q : ℕ) [NeZero q] [Fact (Nat.Prime q)]

/-- The $L^2$ norm of $f : (\mathbb{Z}/q)^* \to \mathbb{C}$ on the unit group,
$\|f\|_{L^2((\mathbb{Z}/q)^*)} = \bigl(\sum_{b \in (\mathbb{Z}/q)^*} |f(b)|^2\bigr)^{1/2}$. -/
def l2NormUnits (f : (ZMod q)ˣ → ℂ) : ℝ :=
  Real.sqrt (∑ b : (ZMod q)ˣ, ‖f b‖ ^ 2)

/-- The multiplicative convolution on units `mulConvUnits` agrees pointwise with the generic
multiplicative convolution `MultiplicativeConvolution.mulConv` on the unit group. -/
lemma mulConvUnits_eq_mulConv (f g : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) :
    mulConvUnits q f g a = MultiplicativeConvolution.mulConv f g a := by
  simp only [mulConvUnits, MultiplicativeConvolution.mulConv, div_eq_mul_inv]

/-- The unit-group $L^2$ norm `l2NormUnits` agrees with the generic `l2Norm` from
`MultiplicativeConvolution`. -/
lemma l2NormUnits_eq_l2Norm (f : (ZMod q)ˣ → ℂ) :
    l2NormUnits q f = MultiplicativeConvolution.l2Norm f := by
  simp only [l2NormUnits, MultiplicativeConvolution.l2Norm]

/-- Pointwise high-frequency $L^\infty$ bound on the multiplicative convolution:
for every $a \in (\mathbb{Z}/q)^*$,
$|(f *_M g)_h(a)| \le \|f_h\|_{L^2((\mathbb{Z}/q)^*)} \, \|g_h\|_{L^2((\mathbb{Z}/q)^*)}$. -/
theorem norm_highFreq_mulConvUnits_le
    (f g : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) :
    ‖highFreqUnits q (mulConvUnits q f g) a‖ ≤
      l2NormUnits q (highFreqUnits q f) * l2NormUnits q (highFreqUnits q g) := by
  have h4 := highFreq_mulConvUnits q f g
  rw [show highFreqUnits q (mulConvUnits q f g) a =
    mulConvUnits q (highFreqUnits q f) (highFreqUnits q g) a from
    congr_fun h4 a]
  rw [mulConvUnits_eq_mulConv]
  rw [l2NormUnits_eq_l2Norm, l2NormUnits_eq_l2Norm]
  exact MultiplicativeConvolution.norm_mulConv_le _ _ a

/-- Multiplicative convolution $L^\infty$ bound on the units (high-frequency part):
$\|(f *_M g)_h\|_{L^\infty((\mathbb{Z}/q)^*)} \le \|f_h\|_{L^2} \, \|g_h\|_{L^2}$. -/
theorem highFreq_mulConv_linfty_le_l2_l2
    (f g : (ZMod q)ˣ → ℂ) :
    (⨆ a : (ZMod q)ˣ, ‖highFreqUnits q (mulConvUnits q f g) a‖) ≤
      l2NormUnits q (highFreqUnits q f) * l2NormUnits q (highFreqUnits q g) := by
  apply ciSup_le
  exact norm_highFreq_mulConvUnits_le q f g

/-- Restrict a function $F : \mathbb{Z}/q \to \mathbb{C}$ to the unit group
$(\mathbb{Z}/q)^*$ by composing with the natural map $u \mapsto (u : \mathbb{Z}/q)$. -/
def restrictToUnits (F : ZMod q → ℂ) : (ZMod q)ˣ → ℂ :=
  fun u => F (↑u : ZMod q)

/-- The $L^2$ norm of $F : \mathbb{Z}/q \to \mathbb{C}$,
$\|F\|_{L^2(\mathbb{Z}/q)} = \bigl(\sum_{a} |F(a)|^2\bigr)^{1/2}$. -/
def l2Norm_ZMod (F : ZMod q → ℂ) : ℝ :=
  Real.sqrt (LinnikLargeSieve.l2NormSq_ZMod q F)

/-- For $u \in (\mathbb{Z}/q)^*$, the mod-$q$ multiplicative convolution of $F, G : \mathbb{Z}/q
\to \mathbb{C}$ evaluated at $u$ agrees with the unit-group multiplicative convolution of the
restrictions $F|_{(\mathbb{Z}/q)^*}$ and $G|_{(\mathbb{Z}/q)^*}$. -/
lemma mulConv_ZMod_units_eq_mulConvUnits
    (F G : ZMod q → ℂ) (u : (ZMod q)ˣ) :
    MultiplicativeConvolution.mulConv_ZMod q F G (↑u : ZMod q) =
    mulConvUnits q (restrictToUnits q F) (restrictToUnits q G) u := by
  simp only [MultiplicativeConvolution.mulConv_ZMod, mulConvUnits, restrictToUnits]
  have hu_ne : (↑u : ZMod q) ≠ 0 := Units.ne_zero u
  have h_inner : ∀ b : ZMod q,
      (∑ c : ZMod q, if b * c = (↑u : ZMod q) then F b * G c else 0) =
      if b ≠ 0 then F b * G ((↑u : ZMod q) * b⁻¹) else 0 := by
    intro b
    by_cases hb : b = 0
    · subst hb
      simp only [zero_mul, ne_eq, not_true, ite_false]
      apply Finset.sum_eq_zero; intro c _
      simp [hu_ne.symm]
    · simp only [hb, ne_eq, not_false_eq_true, ite_true]
      have hiff : ∀ c : ZMod q, (b * c = (↑u : ZMod q)) ↔ (c = (↑u : ZMod q) * b⁻¹) := by
        intro c
        constructor
        · intro h
          have h1 : c = b⁻¹ * (↑u : ZMod q) := by
            have := congr_arg (b⁻¹ * ·) h
            simp only [← mul_assoc, inv_mul_cancel₀ hb, one_mul] at this
            exact this
          rw [h1, mul_comm]
        · intro h
          rw [h, mul_comm (↑u : ZMod q) b⁻¹, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
      conv_lhs => arg 2; ext c; rw [show (if b * c = ↑u then F b * G c else 0) =
        (if c = (↑u : ZMod q) * b⁻¹ then F b * G c else 0) from by
        congr 1; exact propext (hiff c)]
      simp [Finset.sum_ite_eq', Finset.mem_univ]
  simp_rw [h_inner]
  have h_filter : (∑ b : ZMod q, if b ≠ 0 then F b * G (↑u * b⁻¹) else 0) =
      ∑ b ∈ univ.filter (fun b : ZMod q => b ≠ 0), F b * G (↑u * b⁻¹) := by
    rw [Finset.sum_filter]
  rw [h_filter]
  have h_image : univ.filter (fun b : ZMod q => b ≠ 0) =
      univ.image (fun v : (ZMod q)ˣ => (↑v : ZMod q)) := by
    ext x; simp only [mem_filter, mem_univ, true_and, mem_image]
    exact ⟨fun hx => ⟨Units.mk0 x hx, rfl⟩,
           fun ⟨v, hv⟩ => hv ▸ Units.ne_zero v⟩
  rw [h_image, Finset.sum_image (by intro a _ b _ h; exact Units.ext h)]
  congr 1; ext b; congr 1
  rw [Units.val_div_eq_div_val, div_eq_mul_inv]

/-- Functional form: restricting the mod-$q$ multiplicative convolution of $F, G$ to the unit
group equals the unit-group multiplicative convolution of the restrictions. -/
lemma restrictToUnits_mulConv_ZMod_eq
    (F G : ZMod q → ℂ) :
    restrictToUnits q (MultiplicativeConvolution.mulConv_ZMod q F G) =
    mulConvUnits q (restrictToUnits q F) (restrictToUnits q G) := by
  funext u
  exact mulConv_ZMod_units_eq_mulConvUnits q F G u

/-- Comparison of $L^2$ norms of high-frequency parts:
$\|(F^*)_h\|_{L^2((\mathbb{Z}/q)^*)} \le \|F_h\|_{L^2(\mathbb{Z}/q)}$, where $F^*$ is the
restriction of $F$ to the unit group. This is Lemma 3 from §7.3 of the textbook. -/
lemma l2NormUnits_highFreq_restrict_le (F : ZMod q → ℂ) :
    l2NormUnits q (highFreqUnits q (restrictToUnits q F)) ≤
    l2Norm_ZMod q (LinnikLargeSieve.highFreqPart_ZMod q F) := by
  unfold l2NormUnits l2Norm_ZMod LinnikLargeSieve.l2NormSq_ZMod
  apply Real.sqrt_le_sqrt


  show ∑ u : (ZMod q)ˣ, ‖highFreqUnits q (restrictToUnits q F) u‖ ^ 2 ≤
    ∑ a : ZMod q, ‖LinnikLargeSieve.highFreqPart_ZMod q F a‖ ^ 2
  simp only [highFreqUnits, restrictToUnits, LinnikLargeSieve.highFreqPart_ZMod]
  set μ := (1 / (q : ℂ)) * ∑ b : ZMod q, F b
  set μ_star := (∑ v : (ZMod q)ˣ, F (↑v)) / (Fintype.card (ZMod q)ˣ : ℂ)

  have h_zero : ∑ u : (ZMod q)ˣ, (F (↑u) - μ_star) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, μ_star]
    have hn : (Fintype.card (ZMod q)ˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp; ring
  have h_min : ∑ u : (ZMod q)ˣ, ‖F (↑u) - μ_star‖ ^ 2 ≤
      ∑ u : (ZMod q)ˣ, ‖F (↑u) - μ‖ ^ 2 := by
    have h_diff : ∀ u : (ZMod q)ˣ,
        ‖F (↑u) - μ‖ ^ 2 - ‖F (↑u) - μ_star‖ ^ 2 =
        ‖μ_star - μ‖ ^ 2 + 2 * @inner ℝ ℂ _ (F (↑u) - μ_star) (μ_star - μ) := by
      intro u
      have : F (↑u) - μ = (F (↑u) - μ_star) + (μ_star - μ) := by ring
      rw [this, norm_add_sq_real]; ring
    have h_sum_diff : ∑ u : (ZMod q)ˣ, (‖F (↑u) - μ‖ ^ 2 - ‖F (↑u) - μ_star‖ ^ 2) =
        (Fintype.card (ZMod q)ˣ : ℝ) * ‖μ_star - μ‖ ^ 2 := by
      simp_rw [h_diff, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum]
      have h_cross : ∑ u : (ZMod q)ˣ, @inner ℝ ℂ _ (F (↑u) - μ_star) (μ_star - μ) = 0 := by
        rw [← sum_inner (𝕜 := ℝ), h_zero, inner_zero_left]
      linarith [h_cross]
    have h_nonneg : 0 ≤ ∑ u : (ZMod q)ˣ, (‖F (↑u) - μ‖ ^ 2 - ‖F (↑u) - μ_star‖ ^ 2) := by
      rw [h_sum_diff]
      exact mul_nonneg (Nat.cast_nonneg' _) (sq_nonneg _)
    linarith [Finset.sum_sub_distrib
      (f := fun u : (ZMod q)ˣ => ‖F (↑u) - μ‖ ^ 2)
      (g := fun u : (ZMod q)ˣ => ‖F (↑u) - μ_star‖ ^ 2)
      (s := Finset.univ)]

  have h_subset : ∑ u : (ZMod q)ˣ, ‖F (↑u) - μ‖ ^ 2 ≤
      ∑ a : ZMod q, ‖F a - μ‖ ^ 2 := by
    have h_eq : ∑ u : (ZMod q)ˣ, ‖F (↑u) - μ‖ ^ 2 =
        ∑ a ∈ univ.filter (fun x : ZMod q => x ≠ 0), ‖F a - μ‖ ^ 2 := by
      rw [show univ.filter (fun x : ZMod q => x ≠ 0) =
        univ.image (fun v : (ZMod q)ˣ => (↑v : ZMod q)) from by
        ext x; simp only [mem_filter, mem_univ, true_and, mem_image]
        exact ⟨fun hx => ⟨Units.mk0 x hx, rfl⟩, fun ⟨v, hv⟩ => hv ▸ Units.ne_zero v⟩]
      rw [Finset.sum_image (by intro a _ b _ h; exact Units.ext h)]
    rw [h_eq]
    apply Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro a _ _; positivity
  linarith

/-- Full-version $L^\infty$ bound: for $f, g : \mathbb{N} \to \mathbb{C}$ supported on
$[1, N)$,
$$\|(\pi_q(f *_M g))^*_h\|_{L^\infty((\mathbb{Z}/q)^*)} \le
  \|(\pi_q f)_h\|_{L^2(\mathbb{Z}/q)} \, \|(\pi_q g)_h\|_{L^2(\mathbb{Z}/q)},$$
where the left side is the high-frequency part on units of the projection of the
multiplicative convolution. -/
theorem highFreq_mulConv_linfty_le_l2_l2_full
    (N : ℕ) (f g : ℕ → ℂ)
    (_hf : ∀ n, N ≤ n → f n = 0) (_hg : ∀ n, N ≤ n → g n = 0)
    (_hf0 : f 0 = 0) (_hg0 : g 0 = 0) :
    (⨆ a : (ZMod q)ˣ, ‖highFreqUnits q
      (restrictToUnits q (MultiplicativeConvolution.mulConv_ZMod q
        (MultiplicativeConvolution.modProjection_arith N q f)
        (MultiplicativeConvolution.modProjection_arith N q g))) a‖) ≤
    l2Norm_ZMod q (LinnikLargeSieve.highFreqPart_ZMod q
      (MultiplicativeConvolution.modProjection_arith N q f)) *
    l2Norm_ZMod q (LinnikLargeSieve.highFreqPart_ZMod q
      (MultiplicativeConvolution.modProjection_arith N q g)) := by
  set F := MultiplicativeConvolution.modProjection_arith N q f
  set G := MultiplicativeConvolution.modProjection_arith N q g

  have h_restrict : restrictToUnits q (MultiplicativeConvolution.mulConv_ZMod q F G) =
      mulConvUnits q (restrictToUnits q F) (restrictToUnits q G) :=
    restrictToUnits_mulConv_ZMod_eq q F G
  simp_rw [h_restrict]

  have step2 := highFreq_mulConv_linfty_le_l2_l2 q (restrictToUnits q F) (restrictToUnits q G)

  have step3f := l2NormUnits_highFreq_restrict_le q F
  have step3g := l2NormUnits_highFreq_restrict_le q G

  calc (⨆ a : (ZMod q)ˣ, ‖highFreqUnits q
        (mulConvUnits q (restrictToUnits q F) (restrictToUnits q G)) a‖)
      ≤ l2NormUnits q (highFreqUnits q (restrictToUnits q F)) *
        l2NormUnits q (highFreqUnits q (restrictToUnits q G)) := step2
    _ ≤ l2Norm_ZMod q (LinnikLargeSieve.highFreqPart_ZMod q F) *
        l2Norm_ZMod q (LinnikLargeSieve.highFreqPart_ZMod q G) := by
      apply mul_le_mul step3f step3g
      · unfold l2NormUnits; positivity
      · unfold l2Norm_ZMod LinnikLargeSieve.l2NormSq_ZMod; positivity

end HighFreqMultConv
