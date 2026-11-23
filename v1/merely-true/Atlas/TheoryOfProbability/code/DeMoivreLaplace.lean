/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.CDF
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Measure.LevyConvergence

open MeasureTheory ProbabilityTheory Filter
open scoped unitInterval NNReal Topology Real

noncomputable section

namespace ProbabilityTheory

/-- **Standardized binomial distribution**.

The law of `(Sₙ − np) / √(np(1−p))` where `Sₙ ~ Binomial(n, p)`. This is the
standardized sum appearing in the DeMoivre–Laplace limit theorem. -/
def standardizedBinomial (n : ℕ) (p : I) : Measure ℝ :=
  Bin(ℝ, n, p).map (fun x : ℝ ↦ (x - ↑n * ↑p) / Real.sqrt (↑n * ↑p * (1 - ↑p)))

/-- The real-valued binomial measure `Bin(ℝ, n, p)` is a probability measure. -/
instance isProbabilityMeasure_Bin_real (n : ℕ) (p : I) :
    IsProbabilityMeasure Bin(ℝ, n, p) :=
  Measure.isProbabilityMeasure_map measurable_from_top.aemeasurable

/-- The standardized binomial measure is a probability measure (pushforward of a
probability measure under a measurable affine map). -/
instance isProbabilityMeasure_standardizedBinomial (n : ℕ) (p : I) :
    IsProbabilityMeasure (standardizedBinomial n p) := by
  unfold standardizedBinomial
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Bundled `ProbabilityMeasure` wrapper around `standardizedBinomial n p`. -/
def standardizedBinomialProb (n : ℕ) (p : I) : ProbabilityMeasure ℝ :=
  ⟨standardizedBinomial n p, isProbabilityMeasure_standardizedBinomial n p⟩

/-- The **standard normal** distribution `N(0, 1)` packaged as a `ProbabilityMeasure ℝ`. -/
def stdNormalProb : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

/-- **Characteristic function of the standard normal**: `φ_Z(t) = exp(−t² / 2)`. -/
lemma charFun_stdNormal (t : ℝ) :
    charFun (gaussianReal 0 (1 : NNReal)) t = Complex.exp (-(t ^ 2 / 2)) := by
  rw [charFun_gaussianReal]
  simp [NNReal.coe_one]

/-- **Affine transformation of a characteristic function.**

If `Y = (X − a)/s` then `φ_Y(t) = φ_X(t/s) · exp(−i a t / s)`. -/
lemma charFun_map_affine (μ : Measure ℝ) (a s t : ℝ) :
    charFun (μ.map (fun x => (x - a) / s)) t =
      charFun μ (t * s⁻¹) * Complex.exp (↑(-(a * (t * s⁻¹))) * Complex.I) := by
  have decomp : μ.map (fun x => (x - a) / s) =
      (μ.map (fun x => x + (-a))).map (fun x => s⁻¹ * x) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1; ext x; simp [Function.comp, sub_eq_add_neg, div_eq_mul_inv, mul_comm]
  rw [decomp, charFun_map_mul, charFun_map_add_const]
  congr 1
  · congr 1; ring
  · congr 1; congr 1
    unfold inner InnerProductSpace.toInner
    simp only [RCLike.toInnerProductSpaceReal, Inner.rclikeToReal]
    simp [RCLike.inner_apply, mul_comm]

/-- **Point mass formula for the binomial distribution.**

For `k ≤ n`, `Binomial(n, p)({k}) = C(n, k) · pᵏ · (1−p)ⁿ⁻ᵏ`. -/
lemma binomial_singleton (n k : ℕ) (p : I) (hk : k ≤ n) :
    (binomial n p) {k} = n.choose k * (unitInterval.toNNReal p) ^ k *
      (unitInterval.toNNReal (σ p)) ^ (n - k) := by
  unfold binomial
  rw [Measure.map_apply (by fun_prop) (by measurability)]
  set F := (Finset.Iio n).powersetCard k

  have hae_eq : setBer(Set.Iio n, p) (Set.ncard ⁻¹' {k}) =
      setBer(Set.Iio n, p) (⋃ t ∈ F, {(↑t : Set ℕ)}) := by
    apply measure_congr
    filter_upwards [setBernoulli_ae_subset] with s hs
    apply propext; constructor
    · intro hmem
      change s.ncard = k at hmem
      have hfin_s : s.Finite := Set.Finite.subset (Set.finite_Iio n) hs
      change s ∈ ⋃ t ∈ F, {(↑t : Set ℕ)}; rw [Set.mem_iUnion₂]
      refine ⟨hfin_s.toFinset, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        exact ⟨fun x hx => by
          simp only [Finset.mem_Iio]; exact hs (hfin_s.mem_toFinset.mp hx), by
          rw [← hmem]; exact (Set.ncard_eq_toFinset_card _ hfin_s).symm⟩
      · rw [Set.mem_singleton_iff]; exact (Set.Finite.coe_toFinset hfin_s).symm
    · intro hmem
      change s ∈ ⋃ t ∈ F, {(↑t : Set ℕ)} at hmem; change s.ncard = k
      rw [Set.mem_iUnion₂] at hmem; obtain ⟨t, ht, hs_eq⟩ := hmem
      rw [Set.mem_singleton_iff] at hs_eq
      rw [hs_eq, Set.ncard_coe_finset]; exact (Finset.mem_powersetCard.mp ht).2

  have hsum : setBer(Set.Iio n, p) (⋃ t ∈ F, {(↑t : Set ℕ)}) =
      ∑ t ∈ F, setBer(Set.Iio n, p) {(↑t : Set ℕ)} := by
    apply measure_biUnion_finset
    · intro t₁ _ t₂ _ hne; exact Set.disjoint_singleton.mpr (Finset.coe_injective.ne hne)
    · intro t _; exact MeasurableSet.singleton _

  have hterm : ∀ t ∈ F, setBer(Set.Iio n, p) {(↑t : Set ℕ)} =
      (unitInterval.toNNReal p) ^ k * (unitInterval.toNNReal (σ p)) ^ (n - k) := by
    intro t ht
    have hsub : (↑t : Set ℕ) ⊆ Set.Iio n := by
      intro x hx
      have hmem := (Finset.mem_powersetCard.mp ht).1 (Finset.mem_coe.mp hx)
      simp [Finset.mem_Iio] at hmem; exact hmem
    rw [setBernoulli_singleton _ _ hsub (Set.finite_Iio n)]
    have h_ncard_t : (↑t : Set ℕ).ncard = k := by
      rw [Set.ncard_coe_finset]; exact (Finset.mem_powersetCard.mp ht).2
    have h_ncard_diff : (Set.Iio n \ ↑t).ncard = n - k := by
      rw [Set.ncard_diff hsub, h_ncard_t, Set.ncard_eq_toFinset_card']; simp
    rw [h_ncard_t, h_ncard_diff]

  rw [hae_eq, hsum, Finset.sum_congr rfl hterm, Finset.sum_const]
  rw [Finset.card_powersetCard]; simp; ring

/-- The binomial distribution `Binomial(n, p)` assigns mass zero to any `k > n`. -/
lemma binomial_singleton_of_gt (n k : ℕ) (p : I) (hk : n < k) :
    (binomial n p) {k} = 0 := by
  unfold binomial
  rw [Measure.map_apply (by fun_prop) (by measurability)]
  have hae : ∀ᵐ s ∂setBer(Set.Iio n, p), s ⊆ Set.Iio n := setBernoulli_ae_subset
  rw [Filter.Eventually, MeasureTheory.mem_ae_iff] at hae
  apply le_antisymm _ (zero_le _)
  calc setBer(Set.Iio n, p) (Set.ncard ⁻¹' {k})
      ≤ setBer(Set.Iio n, p) {s | ¬ s ⊆ Set.Iio n} := by
        apply measure_mono
        intro s hs
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hs
        simp only [Set.mem_setOf_eq]
        intro hsub
        have h1 : s.ncard ≤ (Set.Iio n).ncard := Set.ncard_le_ncard hsub (Set.finite_Iio n)
        have h2 : (Set.Iio n).ncard = n := by rw [Set.ncard_eq_toFinset_card']; simp
        omega
    _ = 0 := hae

/-- Every function `f : ℕ → ℂ` is integrable against `Binomial(n, p)` since the
distribution is supported on the finite set `{0, …, n}`. -/
lemma integrable_binomial (n : ℕ) (p : I) (f : ℕ → ℂ) :
    Integrable f (binomial n p) := by
  rw [Integrable, and_iff_right (by measurability)]
  rw [HasFiniteIntegral, lintegral_countable']
  have hsup : ∀ a, a ∉ Finset.range (n + 1) →
      ‖f a‖₊ * (binomial n p) {a} = 0 := by
    intro k hk; rw [Finset.mem_range, not_lt] at hk
    simp [binomial_singleton_of_gt n k p (by omega)]
  calc ∑' a, ‖f a‖₊ * (binomial n p) {a}
      = ∑ a ∈ Finset.range (n + 1), ‖f a‖₊ * (binomial n p) {a} := tsum_eq_sum hsup
    _ < ⊤ := by rw [ENNReal.sum_lt_top]; intro k _
                exact ENNReal.mul_lt_top (by finiteness) (measure_lt_top _ _)

/-- Real-valued version of the binomial point mass formula:
`Binomial(n, p)({k}) = C(n, k) · pᵏ · (1−p)ⁿ⁻ᵏ` as a real number. -/
lemma binomial_singleton_toReal (n k : ℕ) (p : I) (hk : k ≤ n) :
    ((binomial n p) {k}).toReal =
    (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
  rw [binomial_singleton n k p hk]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_natCast, ENNReal.coe_toReal, ENNReal.coe_toReal]
  simp [unitInterval.toNNReal, unitInterval.symm]

/-- Integrals against the binomial measure are finite sums:
`∫ f d(Binomial(n, p)) = ∑_{k=0}^{n} C(n,k) · pᵏ · (1−p)ⁿ⁻ᵏ · f(k)`. -/
theorem integral_binomial_eq_sum (n : ℕ) (p : I) (f : ℕ → ℂ) :
    ∫ x, f x ∂(binomial n p) = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℂ) * (↑(p : ℝ))^k * (↑(1 - (p : ℝ)))^(n - k) * f k := by
  rw [integral_countable (integrable_binomial n p f)]
  unfold Measure.real
  have hsup : ∀ x, x ∉ Finset.range (n + 1) →
      ((binomial n p) {x}).toReal • f x = 0 := by
    intro k hk; rw [Finset.mem_range, not_lt] at hk
    simp [binomial_singleton_of_gt n k p (by omega)]
  calc ∑' x, ((binomial n p) {x}).toReal • f x
      = ∑ x ∈ Finset.range (n + 1), ((binomial n p) {x}).toReal • f x := tsum_eq_sum hsup
    _ = _ := by
        apply Finset.sum_congr rfl; intro k hk; rw [Finset.mem_range] at hk
        rw [binomial_singleton_toReal n k p (by omega), Complex.real_smul]
        push_cast; ring

/-- **Characteristic function of the real-valued binomial distribution.**

`φ_{Bin(n, p)}(t) = ((1 − p) + p · e^{it})ⁿ`. -/
theorem charFun_binomial_real (n : ℕ) (p : I) (t : ℝ) :
    charFun Bin(ℝ, n, p) t =
      ((1 - (p : ℝ)) + (p : ℝ) * Complex.exp (↑t * Complex.I)) ^ n := by

  have h1 : charFun Bin(ℝ, n, p) t =
      ∫ k, Complex.exp (↑(↑k * t) * Complex.I) ∂(binomial n p) := by
    unfold charFun
    rw [integral_map measurable_from_top.aemeasurable (by fun_prop)]
    congr 1; ext k
    unfold inner InnerProductSpace.toInner
    simp only [RCLike.toInnerProductSpaceReal, Inner.rclikeToReal]
    simp [RCLike.inner_apply, mul_comm]
  rw [h1, integral_binomial_eq_sum n p _]

  set pe : ℂ := ((p : ℝ) : ℂ) * Complex.exp (↑t * Complex.I)
  set q : ℂ := ((1 - (p : ℝ)) : ℂ)
  rw [show q + pe = pe + q from add_comm q pe]
  rw [Commute.add_pow (Commute.all pe q)]
  apply Finset.sum_congr rfl
  intro k hk; rw [Finset.mem_range] at hk
  simp only [pe, mul_pow]
  rw [show (↑(↑k * t) : ℂ) * Complex.I = ↑k * (↑t * Complex.I) by push_cast; ring,
      Complex.exp_nat_mul]
  push_cast; ring

/-- **Characteristic function of the standardized binomial** as a rescaling of the
characteristic function of `Bin(n, p)`. Specialization of `charFun_map_affine` to the
shift `np` and scale `s = √(np(1−p))`. -/
lemma charFun_standardizedBinomial (n : ℕ) (p : I) (t : ℝ) :
    let s := Real.sqrt (↑n * ↑p * (1 - ↑p))
    charFun (standardizedBinomial n p) t =
      charFun Bin(ℝ, n, p) (t * s⁻¹) *
        Complex.exp (↑(-(↑n * (↑p : ℝ) * (t * s⁻¹))) * Complex.I) := by
  intro s
  unfold standardizedBinomial
  exact charFun_map_affine _ _ _ _


/-- **Second-order Taylor remainder bound for `exp`.**

For `‖z‖ ≤ 1`, the remainder after the degree-2 Taylor polynomial of `exp` satisfies
`‖e^z − 1 − z − z²/2‖ ≤ 2 ‖z‖³`. Used in the proof of the DeMoivre–Laplace CLT. -/
lemma exp_taylor2_err (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ ≤ 2 * ‖z‖ ^ 3 := by
  have h := Complex.exp_bound hz (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial,
    Nat.cast_one, div_one, zero_add] at h
  have hconv : ‖Complex.exp z - (1 + z + z ^ 2 / ↑2)‖ ≤ ‖z‖ ^ 3 * (↑4 * (↑6 * ↑3)⁻¹) := by
    convert h using 2; push_cast; ring
  calc ‖Complex.exp z - 1 - z - z ^ 2 / 2‖
      = ‖Complex.exp z - (1 + z + z ^ 2 / ↑2)‖ := by congr 1; ring
    _ ≤ ‖z‖ ^ 3 * (↑4 * (↑6 * ↑3)⁻¹) := hconv
    _ ≤ ‖z‖ ^ 3 * 2 := by gcongr; norm_num
    _ = 2 * ‖z‖ ^ 3 := by ring

/-- **Convergence of characteristic functions in DeMoivre–Laplace.**

For `0 < p < 1` and every `t ∈ ℝ`, the characteristic function of the standardized
binomial converges to the characteristic function of the standard normal:
`φ_{standardizedBinomial n p}(t) → exp(−t² / 2)`.

This is the key analytic step in proving `deMoivreLaplace_clt` via Lévy's continuity
theorem. -/
lemma tendsto_charFun_standardizedBinomial (p : I) (hp₀ : (0 : ℝ) < p) (hp₁ : (p : ℝ) < 1)
    (t : ℝ) :
    Tendsto (fun n ↦ charFun (standardizedBinomial n p) t) atTop
      (𝓝 (Complex.exp (-(t ^ 2 / 2)))) := by

  set pp := (p : ℝ) with hpp
  set qq := 1 - pp with hqq
  have hqq_pos : 0 < qq := by linarith
  have hpp_pos : 0 < pp := hp₀
  have hpq_pos : 0 < pp * qq := mul_pos hpp_pos hqq_pos


  set B : ℕ → ℂ := fun n =>
    let s := Real.sqrt (↑n * pp * qq)
    let u := t * s⁻¹
    ↑qq * Complex.exp (↑(-(pp * u)) * Complex.I) +
      ↑pp * Complex.exp (↑(qq * u) * Complex.I)

  suffices h_conv : Tendsto (fun n => (B n) ^ n) atTop (𝓝 (Complex.exp (-(t ^ 2 / 2)))) by
    apply h_conv.congr
    intro n

    simp only [B]
    rw [charFun_standardizedBinomial, charFun_binomial_real]

    set s := Real.sqrt (↑n * pp * qq)
    set u := t * s⁻¹
    show (↑qq * Complex.exp (↑(-(pp * u)) * Complex.I) + ↑pp * Complex.exp (↑(qq * u) * Complex.I)) ^ n =
      ((1 - pp) + pp * Complex.exp (↑u * Complex.I)) ^ n *
        Complex.exp (↑(-(↑n * pp * u)) * Complex.I)
    rw [show (↑(-(↑n * pp * u)) : ℂ) * Complex.I = ↑n * (↑(-(pp * u)) * Complex.I) by push_cast; ring]
    rw [Complex.exp_nat_mul, ← mul_pow]
    congr 1
    rw [add_mul]
    have hqq_cast : (qq : ℂ) = 1 - (pp : ℂ) := by
      simp only [hqq]; push_cast; ring
    congr 1
    · rw [hqq_cast]
    · rw [mul_assoc, ← Complex.exp_add]
      congr 1
      have : qq * u = u + -(pp * u) := by rw [hqq]; ring
      rw [this]; push_cast; ring

  set z₀ : ℂ := -((↑t : ℂ) ^ 2 / 2)
  apply Complex.tendsto_pow_exp_of_isLittleO_sub_add_div z₀


  rw [Asymptotics.isLittleO_iff]
  intro ε hε


  set K := 2 * |t| ^ 3 / (pp * qq) ^ (3/2 : ℝ)


  have hN_bound : ∀ᶠ (n : ℕ) in atTop, |t| / Real.sqrt (↑n * (pp * qq)) ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop (⌈t ^ 2 / (pp * qq)⌉.toNat + 1)] with n hn
    rw [div_le_one (Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr (by omega)) hpq_pos))]
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    calc t ^ 2 ≤ ⌈t ^ 2 / (pp * qq)⌉ * (pp * qq) := by
          rw [← div_le_iff₀ hpq_pos]; exact Int.le_ceil _
        _ ≤ ↑n * (pp * qq) := by
          gcongr
          have : ⌈t ^ 2 / (pp * qq)⌉.toNat ≤ n := by omega
          calc (⌈t ^ 2 / (pp * qq)⌉ : ℝ)
              ≤ ↑(⌈t ^ 2 / (pp * qq)⌉.toNat : ℤ) := by exact_mod_cast Int.self_le_toNat _
            _ ≤ ↑n := by exact_mod_cast this
  have hK_bound : ∀ᶠ (n : ℕ) in atTop, K / Real.sqrt n ≤ ε := by
    filter_upwards [Filter.eventually_ge_atTop (⌈(K / ε) ^ 2⌉.toNat + 1)] with n hn
    have hn_pos : 0 < n := by omega
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn_pos))]
    have h1 : (K / ε) ^ 2 ≤ ↑n := by
      have : ⌈(K / ε) ^ 2⌉.toNat ≤ n := by omega
      calc (K / ε) ^ 2 ≤ ↑⌈(K / ε) ^ 2⌉ := Int.le_ceil _
        _ ≤ ↑(⌈(K / ε) ^ 2⌉.toNat) := by exact_mod_cast Int.self_le_toNat _
        _ ≤ ↑n := by exact_mod_cast this
    calc K ≤ K / ε * ε := by rw [div_mul_cancel₀]; exact ne_of_gt hε
      _ ≤ Real.sqrt ↑n * ε := by
          gcongr; exact Real.le_sqrt_of_sq_le h1
      _ = ε * Real.sqrt ↑n := mul_comm _ _
  filter_upwards [hN_bound, hK_bound, Filter.eventually_ge_atTop 1] with n hsmall hK_small hn_pos


  set sig := Real.sqrt (↑n * pp * qq) with hsig_def
  set u := t * sig⁻¹ with hu_def
  set a : ℂ := ↑(-(pp * u)) * Complex.I with ha_def
  set b : ℂ := ↑(qq * u) * Complex.I with hb_def
  set R_a := Complex.exp a - 1 - a - a ^ 2 / 2
  set R_b := Complex.exp b - 1 - b - b ^ 2 / 2

  have hB_unfold : B n = ↑qq * Complex.exp a + ↑pp * Complex.exp b := by
    simp only [B, a, b, sig, u]
  have hqq_pp : (↑qq : ℂ) + ↑pp = 1 := by
    push_cast [hqq]; ring
  have hlin : (↑qq : ℂ) * a + ↑pp * b = 0 := by
    simp only [a, b]; push_cast; simp [hqq]; ring
  have hn_pos' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hsig_ne : sig ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hsig_pos : 0 < sig := Real.sqrt_pos.mpr (by positivity)
  have hsig_sq : sig ^ 2 = ↑n * pp * qq := Real.sq_sqrt (by positivity)
  have hquad : (↑qq : ℂ) * (a ^ 2 / 2) + ↑pp * (b ^ 2 / 2) = z₀ / ↑↑n := by
    have ha2 : a ^ 2 = -(↑(pp * u) : ℂ) ^ 2 := by
      simp only [a]; rw [mul_pow, Complex.I_sq]; push_cast; ring
    have hb2 : b ^ 2 = -(↑(qq * u) : ℂ) ^ 2 := by
      simp only [b]; rw [mul_pow, Complex.I_sq]; push_cast; ring
    rw [ha2, hb2]
    have h : (qq * (-(pp * u) ^ 2 / 2) + pp * (-(qq * u) ^ 2 / 2) : ℝ) = -(t ^ 2 / 2) / ↑n := by
      show qq * (-(pp * (t * sig⁻¹)) ^ 2 / 2) + pp * (-(qq * (t * sig⁻¹)) ^ 2 / 2) = -(t ^ 2 / 2) / ↑n
      rw [hqq]; rw [hqq] at hsig_sq; field_simp; rw [hsig_sq]; ring
    have := congr_arg (fun (x : ℝ) => (x : ℂ)) h
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow,
               Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat] at this
    convert this using 1 <;> push_cast <;> ring
  have hBR : B n - (1 + z₀ / ↑↑n) = ↑qq * R_a + ↑pp * R_b := by
    have hexp_a : Complex.exp a = 1 + a + a ^ 2 / 2 + R_a := by simp [R_a]
    have hexp_b : Complex.exp b = 1 + b + b ^ 2 / 2 + R_b := by simp [R_b]
    rw [hB_unfold, hexp_a, hexp_b]
    have : ↑qq * (1 + a + a ^ 2 / 2 + R_a) + ↑pp * (1 + b + b ^ 2 / 2 + R_b) - (1 + z₀ / ↑↑n) =
      (↑qq + ↑pp - 1) + (↑qq * a + ↑pp * b) + (↑qq * (a ^ 2 / 2) + ↑pp * (b ^ 2 / 2) - z₀ / ↑↑n) +
      (↑qq * R_a + ↑pp * R_b) := by ring
    rw [this, hqq_pp, hlin, hquad]; ring

  have hsmall_sig : |t| / sig ≤ 1 := by
    rwa [show sig = Real.sqrt (↑n * (pp * qq)) from by rw [hsig_def]; ring_nf]
  have hu_abs : |u| = |t| / sig := by
    rw [hu_def, abs_mul, abs_inv, abs_of_pos hsig_pos, div_eq_mul_inv]
  have ha_norm : ‖a‖ ≤ 1 := by
    simp only [a, Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    calc |-(pp * u)| = pp * |u| := by rw [abs_neg, abs_mul, abs_of_pos hpp_pos]
      _ = pp * (|t| / sig) := by rw [hu_abs]
      _ ≤ 1 * 1 := by
          apply mul_le_mul (le_of_lt hp₁) hsmall_sig (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (by linarith)
      _ = 1 := one_mul 1
  have hb_norm : ‖b‖ ≤ 1 := by
    simp only [b, Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    calc |qq * u| = qq * |u| := by rw [abs_mul, abs_of_pos hqq_pos]
      _ = qq * (|t| / sig) := by rw [hu_abs]
      _ ≤ 1 * 1 := by
          apply mul_le_mul (by linarith) hsmall_sig (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (by linarith)
      _ = 1 := one_mul 1
  have hRa_bound := exp_taylor2_err a ha_norm
  have hRb_bound := exp_taylor2_err b hb_norm
  have ha_le : ‖a‖ ≤ |t| / sig := by
    simp only [a, Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    calc |-(pp * u)| = pp * |u| := by rw [abs_neg, abs_mul, abs_of_pos hpp_pos]
      _ = pp * (|t| / sig) := by rw [hu_abs]
      _ ≤ 1 * (|t| / sig) := by
          apply mul_le_mul_of_nonneg_right (le_of_lt hp₁) (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      _ = |t| / sig := one_mul _
  have hb_le : ‖b‖ ≤ |t| / sig := by
    simp only [b, Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    calc |qq * u| = qq * |u| := by rw [abs_mul, abs_of_pos hqq_pos]
      _ = qq * (|t| / sig) := by rw [hu_abs]
      _ ≤ 1 * (|t| / sig) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      _ = |t| / sig := one_mul _

  have hn_norm : ‖(1 : ℂ) / ↑↑n‖ = 1 / ↑n := by
    rw [one_div, norm_inv, Complex.norm_natCast]
    simp
  rw [hBR, hn_norm]
  calc ‖↑qq * R_a + ↑pp * R_b‖
      ≤ ‖↑qq * R_a‖ + ‖↑pp * R_b‖ := norm_add_le _ _
    _ = qq * ‖R_a‖ + pp * ‖R_b‖ := by
        rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hqq_pos, abs_of_pos hpp_pos]
    _ ≤ qq * (2 * ‖a‖ ^ 3) + pp * (2 * ‖b‖ ^ 3) := by
        gcongr
    _ ≤ qq * (2 * (|t| / sig) ^ 3) + pp * (2 * (|t| / sig) ^ 3) := by
        gcongr
    _ = 2 * (|t| / sig) ^ 3 := by ring_nf; linarith
    _ ≤ ε * (1 / ↑n) := by
        have hn_pos_r : (0 : ℝ) < ↑n := hn_pos'
        rw [div_pow, mul_div, mul_one_div, div_le_div_iff₀ (pow_pos hsig_pos 3) hn_pos_r]
        rw [show sig ^ 3 = sig * sig ^ 2 from by ring, hsig_sq]

        have hK_le : K ≤ ε * Real.sqrt ↑n := by
          calc K = K / Real.sqrt ↑n * Real.sqrt ↑n := by
                rw [div_mul_cancel₀]; exact ne_of_gt (Real.sqrt_pos.mpr hn_pos_r)
            _ ≤ ε * Real.sqrt ↑n := by gcongr
        have h2t3 : 2 * |t| ^ 3 = K * (pp * qq) ^ (3/2 : ℝ) := by
          simp only [K]; field_simp
        have hrpow : (pp * qq) ^ (3/2 : ℝ) = Real.sqrt (pp * qq) * (pp * qq) := by
          rw [Real.sqrt_eq_rpow, show (3 : ℝ)/2 = 1/2 + 1 from by norm_num,
              Real.rpow_add hpq_pos, Real.rpow_one]
        have hsig_eq : sig = Real.sqrt (↑n * (pp * qq)) := by
          rw [← Real.sqrt_sq hsig_pos.le, hsig_sq]; ring_nf
        have hsqrt_prod : Real.sqrt ↑n * Real.sqrt (pp * qq) = sig := by
          rw [hsig_eq, ← Real.sqrt_mul hn_pos_r.le]
        have hkey : Real.sqrt ↑n * (pp * qq) ^ (3/2 : ℝ) * ↑n = sig * (↑n * pp * qq) := by
          rw [hrpow, show Real.sqrt ↑n * (Real.sqrt (pp * qq) * (pp * qq)) * ↑n =
               (Real.sqrt ↑n * Real.sqrt (pp * qq)) * (pp * qq) * ↑n from by ring,
               hsqrt_prod]; ring
        calc 2 * |t| ^ 3 * ↑n
            = K * (pp * qq) ^ (3/2 : ℝ) * ↑n := by rw [h2t3]
          _ ≤ (ε * Real.sqrt ↑n) * (pp * qq) ^ (3/2 : ℝ) * ↑n := by gcongr
          _ = ε * (Real.sqrt ↑n * (pp * qq) ^ (3/2 : ℝ) * ↑n) := by ring
          _ = ε * (sig * (↑n * pp * qq)) := by rw [hkey]

/-- **DeMoivre–Laplace limit theorem** (Lecture 12).

Let `Xᵢ` be i.i.d. Bernoulli(`p`) and `Sₙ = X₁ + ⋯ + Xₙ` so that `Sₙ ~ Binomial(n, p)`.
For `0 < p < 1`, the standardized sums `(Sₙ − np)/√(np(1−p))` converge in distribution
to the standard normal:
`P{a ≤ (Sₙ − np)/√(np(1−p)) ≤ b} → Φ(b) − Φ(a)` as `n → ∞`.

The proof combines `tendsto_charFun_standardizedBinomial` with Lévy's continuity
theorem (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`). -/
theorem deMoivreLaplace_clt (p : I) (hp₀ : (0 : ℝ) < p) (hp₁ : (p : ℝ) < 1) :
    Tendsto (fun n ↦ standardizedBinomialProb n p) atTop (𝓝 stdNormalProb) := by
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t

  have hcf : charFun (↑stdNormalProb : Measure ℝ) t = Complex.exp (-(t ^ 2 / 2)) := by
    show charFun (gaussianReal 0 1) t = _
    exact charFun_stdNormal t

  have hcf_n : ∀ n, charFun (↑(standardizedBinomialProb n p) : Measure ℝ) t =
      charFun (standardizedBinomial n p) t := by
    intro n
    rfl
  simp_rw [hcf_n, hcf]
  exact tendsto_charFun_standardizedBinomial p hp₀ hp₁ t

end ProbabilityTheory
