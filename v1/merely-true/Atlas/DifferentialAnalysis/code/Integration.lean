/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.EReal.Operations

noncomputable section

open MeasureTheory ENNReal Set

namespace Integration

variable {X : Type*} [MeasurableSpace X]

/-- The Lebesgue integral of a nonnegative `ℝ≥0∞`-valued function over a set `E`
with respect to a measure `μ`. -/
abbrev lebesgueIntegralNonneg (μ : Measure X) (f : X → ℝ≥0∞) (E : Set X) : ℝ≥0∞ :=
  ∫⁻ x in E, f x ∂μ

end Integration

namespace LebesgueIntegration

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Integrability on `E` for an `EReal`-valued function: both the positive and the
negative parts have finite Lebesgue integral over `E`. -/
def integrableOnEReal (f : X → EReal) (E : Set X) (μ : Measure X := by volume_tac) : Prop :=
  ∫⁻ x in E, (f x).toENNReal ∂μ ≠ ⊤ ∧ ∫⁻ x in E, (-f x).toENNReal ∂μ ≠ ⊤

/-- Integrability on `E` for a real-valued function, defined via Mathlib's
`IntegrableOn` (Melrose Def 4.1). -/
abbrev integrableOn (f : X → ℝ) (E : Set X) (μ : Measure X := by volume_tac) : Prop :=
  MeasureTheory.IntegrableOn f E μ

/-- The signed Lebesgue integral of a real-valued function over `E` with respect to
`μ` (Melrose Def 4.4). -/
abbrev signedIntegral (f : X → ℝ) (E : Set X) (μ : Measure X := by volume_tac) : ℝ :=
  ∫ x in E, f x ∂μ

end LebesgueIntegration

namespace NormedSpaces

/-- A `𝕜`-normed space `V` is a Banach space iff it is complete. -/
abbrev IsBanachSpace (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (V : Type*) [NormedAddCommGroup V] [NormedSpace 𝕜 V] : Prop := CompleteSpace V

section LpBanach

open MeasureTheory

/-- For `1 ≤ p ≤ ∞`, the space `L^p(μ; E)` valued in a Banach space `E` is itself
a Banach space. -/
theorem Lp_isBanachSpace
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p : ENNReal} [Fact (1 ≤ p)] :
    IsBanachSpace ℝ (Lp E p μ) :=
  Lp.instCompleteSpace

end LpBanach

open scoped ENNReal

section MinkowskiInequality

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E]

/-- Minkowski's inequality in `L^p` for `1 < p ≤ ∞`: the `L^p`-seminorm satisfies the
triangle inequality. -/
theorem minkowski_inequality_eLpNorm {p : ℝ≥0∞}
    (hp_one : 1 < p)
    {f g : α → E}
    (hf : MemLp f p μ) (hg : MemLp g p μ) :
    eLpNorm (f + g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ :=
  eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable hp_one.le

end MinkowskiInequality

end NormedSpaces

namespace Integration

section LIntegralZero

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Vanishing of the Lebesgue integral over `E` is equivalent to the set
`{x ∈ E | f x > 0}` having measure zero. -/
theorem lintegral_eq_zero_iff_measure_pos_eq_zero
    {f : α → ℝ≥0∞} (hf : Measurable f) {E : Set α} (hE : MeasurableSet E) :
    ∫⁻ x in E, f x ∂μ = 0 ↔ μ {x ∈ E | 0 < f x} = 0 := by
  rw [setLIntegral_eq_zero_iff hE hf, ae_iff]
  have : {a | ¬(a ∈ E → f a = 0)} = {x ∈ E | 0 < f x} := by
    ext x
    simp only [mem_setOf_eq, _root_.not_imp, pos_iff_ne_zero, ne_eq]
  rw [this]

end LIntegralZero

/-- Two-term weighted AM-GM inequality: `a^γ b^{1-γ} ≤ γ a + (1-γ) b` for nonnegative
reals and `γ ∈ (0, 1)`. -/
theorem rpow_mul_rpow_le_add (a b γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    a ^ γ * b ^ (1 - γ) ≤ γ * a + (1 - γ) * b :=
  Real.geom_mean_le_arith_mean2_weighted hγ₀.le (by linarith) ha hb (by linarith)

/-- Strict weighted AM-GM: if `a ≠ b`, the inequality `a^γ b^{1-γ} ≤ γ a + (1-γ) b`
is strict. -/
theorem rpow_mul_rpow_lt_add (a b γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hab : a ≠ b) :
    a ^ γ * b ^ (1 - γ) < γ * a + (1 - γ) * b := by
  open Finset in
  let w : Fin 2 → ℝ := ![γ, 1 - γ]
  let z : Fin 2 → ℝ := ![a, b]
  have hw : ∀ i ∈ (univ : Finset (Fin 2)), 0 < w i := by
    intro i _; fin_cases i
    · simp [w]; exact hγ₀
    · simp [w]; linarith
  have hw' : ∑ i ∈ (univ : Finset (Fin 2)), w i = 1 := by
    simp [Fin.sum_univ_two, w, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hz : ∀ i ∈ (univ : Finset (Fin 2)), 0 ≤ z i := by
    intro i _; fin_cases i
    · simp [z]; exact ha
    · simp [z]; exact hb
  have key := (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos univ w z hw hw' hz).mpr
    ⟨0, mem_univ _, 1, mem_univ _, by simp [z]; exact hab⟩
  simp only [Fin.prod_univ_two, Fin.sum_univ_two, w, z] at key
  simpa using key

/-- Equality case in the weighted AM-GM inequality: `a^γ b^{1-γ} = γ a + (1-γ) b` iff
`a = b`. -/
theorem rpow_mul_rpow_eq_add_iff (a b γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    a ^ γ * b ^ (1 - γ) = γ * a + (1 - γ) * b ↔ a = b := by
  constructor
  · intro heq
    by_contra hab
    exact absurd heq (ne_of_lt (rpow_mul_rpow_lt_add a b γ ha hb hγ₀ hγ₁ hab))
  · intro heq
    subst heq
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp [Real.zero_rpow (ne_of_gt hγ₀), Real.zero_rpow (by linarith : (1 : ℝ) - γ ≠ 0)]
    · rw [← Real.rpow_add ha', add_sub_cancel, Real.rpow_one]; ring

/-- Combined weighted AM-GM: the inequality together with the equality characterisation. -/
theorem rpow_mul_rpow_le_add_and_eq_iff {a b γ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hγ₁ : 0 < γ) (hγ₂ : γ < 1) :
    a ^ γ * b ^ (1 - γ) ≤ γ * a + (1 - γ) * b ∧
    (a ^ γ * b ^ (1 - γ) = γ * a + (1 - γ) * b ↔ a = b) :=
  ⟨rpow_mul_rpow_le_add a b γ ha hb hγ₁ hγ₂, rpow_mul_rpow_eq_add_iff a b γ ha hb hγ₁ hγ₂⟩

/-- Hölder's inequality for conjugate exponents `p, q`: the integral of `f * g` is
bounded by the product of the `L^p` and `L^q` norms. -/
theorem holder_inequality {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    |∫ a, f a * g a ∂μ| ≤
      (∫ a, |f a| ^ p ∂μ) ^ (1 / p) * (∫ a, |g a| ^ q ∂μ) ^ (1 / q) := by
  calc |∫ a, f a * g a ∂μ|
      _ ≤ ∫ a, |f a * g a| ∂μ := abs_integral_le_integral_abs
      _ = ∫ a, |f a| * |g a| ∂μ := by
          congr 1; ext a; exact abs_mul (f a) (g a)
      _ = ∫ a, ‖f a‖ * ‖g a‖ ∂μ := by
          simp_rw [← Real.norm_eq_abs]
      _ ≤ (∫ a, ‖f a‖ ^ p ∂μ) ^ (1 / p) * (∫ a, ‖g a‖ ^ q ∂μ) ^ (1 / q) :=
          integral_mul_norm_le_Lp_mul_Lq hpq hf hg
      _ = (∫ a, |f a| ^ p ∂μ) ^ (1 / p) * (∫ a, |g a| ^ q ∂μ) ^ (1 / q) := by
          simp_rw [Real.norm_eq_abs]

/-- Fatou's lemma: for a sequence of nonnegative measurable functions, the integral of
the lower limit is at most the lower limit of the integrals. -/
theorem fatou_lemma
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) :
    ∫⁻ a, Filter.atTop.liminf (fun n => f n a) ∂μ ≤
    Filter.atTop.liminf (fun n => ∫⁻ a, f n a ∂μ) :=
  lintegral_liminf_le hf

end Integration

namespace MonotoneConvergence

open MeasureTheory Filter ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The pointwise supremum of a countable family of measurable functions is measurable. -/
theorem monotone_convergence_measurable
    {f : ℕ → α → ENNReal} (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => ⨆ n, f n x) :=
  Measurable.iSup hf

/-- Monotone convergence (supremum form): the integral commutes with the pointwise
supremum for a monotone sequence of measurable functions. -/
theorem monotone_convergence_iSup
    {f : ℕ → α → ENNReal} (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f)
    {E : Set α} :
    ∫⁻ x in E, (⨆ n, f n x) ∂μ = ⨆ n, ∫⁻ x in E, f n x ∂μ :=
  lintegral_iSup hf h_mono

/-- Monotone convergence (limit form): the integrals of a monotone sequence converge
to the integral of the limit. -/
theorem monotone_convergence_tendsto
    {f : ℕ → α → ENNReal} (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f)
    {E : Set α} :
    Tendsto (fun n => ∫⁻ x in E, f n x ∂μ) atTop
      (𝓝 (∫⁻ x in E, (⨆ n, f n x) ∂μ)) := by
  rw [monotone_convergence_iSup hf h_mono]
  apply tendsto_atTop_iSup
  intro i j hij
  exact lintegral_mono (h_mono hij)

end MonotoneConvergence
