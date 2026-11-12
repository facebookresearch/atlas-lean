/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E]

section IntegralBounds

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Triangle inequality for integrals.** For an integrable function $f : \alpha \to F$ taking
values in a normed space, the norm of the integral is bounded by the integral of the norm:
$\left\|\int f\, d\mu\right\| \le \int \|f\|\, d\mu$. -/
theorem triangle_inequality_integral (f : α → F) :
    ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ :=
  norm_integral_le_integral_norm f

/-- **Basic properties of the Lebesgue integral on $\mathbb{R}$.** This combines three
fundamental statements for measurable real-valued functions $f, g : \alpha \to \mathbb{R}$:
(1) if $f$ is integrable, then $\left|\int f\right| \le \int |f|$;
(2) if $g$ is integrable and $f = g$ almost everywhere, then $f$ is integrable and
$\int f = \int g$;
(3) if $f, g$ are integrable and $f \le g$ almost everywhere, then $\int f \le \int g$. -/
theorem integral_properties :

    (∀ f : α → ℝ, Integrable f μ → ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ) ∧

    (∀ f g : α → ℝ, Integrable g μ → f =ᵐ[μ] g →
      Integrable f μ ∧ ∫ x, f x ∂μ = ∫ x, g x ∂μ) ∧

    (∀ f g : α → ℝ, Integrable f μ → Integrable g μ →
      f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ) :=
  ⟨fun f _ => norm_integral_le_integral_norm f,
   fun _ _ hg hfg => ⟨hg.congr hfg.symm, integral_congr_ae hfg⟩,
   fun _ _ hf hg hle => integral_mono_ae hf hg hle⟩

end IntegralBounds

section LplusAdditivity

/-- **Additivity of the Lebesgue integral on $L^+$.** For measurable functions
$f, g : \alpha \to [0, \infty]$, the Lebesgue integral is additive:
$\int (f + g)\, d\mu = \int f\, d\mu + \int g\, d\mu$. -/
theorem lintegral_add_of_measurable {f g : α → ℝ≥0∞}
    (hf : Measurable f) (_hg : Measurable g) :
    ∫⁻ a, (f a + g a) ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
  lintegral_add_left hf g

end LplusAdditivity

section MonotoneConvergence

open Filter ENNReal

/-- **Monotone Convergence Theorem (supremum form).** If $\{f_n\}$ is a sequence of nonnegative
measurable functions in $L^+(E)$ with $f_1 \le f_2 \le \cdots$ pointwise, then the integral of
the pointwise supremum equals the supremum of the integrals:
$\int \sup_n f_n\, d\mu = \sup_n \int f_n\, d\mu$. -/
theorem monotone_convergence_lintegral {f : ℕ → α → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f) :
    ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ :=
  lintegral_iSup hf h_mono

/-- **Monotone Convergence Theorem (limit form).** If $\{f_n\}$ is a sequence of nonnegative
measurable functions in $L^+(E)$ with $f_1 \le f_2 \le \cdots$ pointwise, and $f_n \to g$
pointwise everywhere, then $\lim_{n \to \infty} \int f_n\, d\mu = \int g\, d\mu$. -/
theorem monotone_convergence_lintegral_tendsto {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f)
    (h_lim : ∀ a, Tendsto (fun n => f n a) atTop (nhds (g a))) :
    Tendsto (fun n => ∫⁻ a, f n a ∂μ) atTop (nhds (∫⁻ a, g a ∂μ)) := by
  have h_eq : (fun a => ⨆ n, f n a) = g := by
    funext a
    exact tendsto_nhds_unique
      (tendsto_atTop_iSup (fun n m hnm => h_mono hnm a))
      (h_lim a)
  conv_rhs => rw [← h_eq]
  simp_rw [monotone_convergence_lintegral hf h_mono]
  exact tendsto_atTop_iSup (fun n m hnm => lintegral_mono (h_mono hnm))

/-- **Fatou's lemma.** For a sequence $\{f_n\}$ of nonnegative measurable functions in $L^+(E)$,
the integral of the pointwise $\liminf$ is bounded by the $\liminf$ of the integrals:
$\int \liminf_{n \to \infty} f_n\, d\mu \le \liminf_{n \to \infty} \int f_n\, d\mu$. -/
theorem fatou_lemma {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  lintegral_liminf_le hf

/-- **A function with finite integral is finite a.e.** If $f \in L^+(E)$ and $\int_E f < \infty$,
then $\{x \in E : f(x) = \infty\}$ has measure zero. -/
theorem measure_setOf_eq_top_of_lintegral_lt_top {f : α → ℝ≥0∞}
    (hf : Measurable f) (hfint : ∫⁻ x, f x ∂μ < ⊤) :
    μ {x | f x = ⊤} = 0 :=
  measure_eq_top_of_lintegral_ne_top hf.aemeasurable hfint.ne

end MonotoneConvergence

section RiemannLebesgueAgree

open Set

variable {F : Type*} [NormedAddCommGroup F]

variable [NormedSpace ℝ F]

/-- **Riemann and Lebesgue integrals agree for continuous functions.** For $f \in C([a, b])$
with $a < b$, the function $f$ is Lebesgue integrable on $[a, b]$, is interval integrable, and
its Lebesgue integral $\int_{[a, b]} f$ coincides with the Riemann integral
$\int_a^b f(x)\, dx$. -/
theorem riemann_lebesgue_agree {f : ℝ → F} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b)) :
    IntegrableOn f (Icc a b) volume ∧
    IntervalIntegrable f volume a b ∧
    ∫ x in Icc a b, f x ∂volume = ∫ x in a..b, f x := by
  refine ⟨hf.integrableOn_Icc, hf.intervalIntegrable_of_Icc hab.le, ?_⟩
  rw [intervalIntegral.integral_of_le hab.le, integral_Icc_eq_integral_Ioc]

end RiemannLebesgueAgree

section DominatedConvergence

open Filter
open scoped Topology

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Dominated Convergence Theorem.** Let $g : \alpha \to [0, \infty)$ be a nonnegative
integrable function, and let $\{F_n\}$ be a sequence of measurable functions such that
(1) $\|F_n\| \le g$ almost everywhere for all $n$ and
(2) $F_n \to f$ pointwise almost everywhere on $\alpha$.
Then $f$ is integrable and $\lim_{n \to \infty} \int F_n\, d\mu = \int f\, d\mu$. -/
theorem dominated_convergence_theorem {F : ℕ → α → G} {f : α → G} {g : α → ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hg_integrable : Integrable g μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ g a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Integrable f μ ∧ Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) := by
  have hf_meas : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hF_meas h_lim
  have hf_bound : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a := by
    have h_all := eventually_countable_forall.mpr h_bound
    filter_upwards [h_all, h_lim] with a ha_bound ha_lim
    exact le_of_tendsto ha_lim.norm (Eventually.of_forall ha_bound)
  exact ⟨hg_integrable.mono' hf_meas hf_bound,
         tendsto_integral_of_dominated_convergence g hF_meas hg_integrable h_bound h_lim⟩

end DominatedConvergence

end MeasureTheory

namespace Integration

section PositiveNegativeParts

variable {α : Type*}

/-- **The integral of a real function as the difference of positive and negative parts.** For
an integrable function $f : \alpha \to \mathbb{R}$, the Lebesgue integral decomposes as
$\int f\, d\mu = \int f^+\, d\mu - \int f^-\, d\mu$, where $f^+ = \max(f, 0)$ and
$f^- = \max(-f, 0)$. -/
theorem integral_eq_posPart_sub_negPart [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f : α → ℝ} (hf : MeasureTheory.Integrable f μ) :
    ∫ x, f x ∂μ = ∫ x, (f x)⁺ ∂μ - ∫ x, (f x)⁻ ∂μ := by
  have h := MeasureTheory.integral_eq_integral_pos_part_sub_integral_neg_part hf
  simp only [posPart_def, negPart_def]
  convert h using 2

end PositiveNegativeParts

end Integration
