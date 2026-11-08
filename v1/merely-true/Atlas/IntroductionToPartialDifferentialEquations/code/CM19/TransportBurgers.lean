/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset MeasureTheory Set

noncomputable section

namespace TransportBurgers

/-- The transport equation $\sum_\mu X^\mu \partial_\mu u = 0$ associated to a
vector field $X$ on $\mathbb{R}^{n+1}$. A function $u$ solves the transport
equation at every point $p$ iff the directional derivative of $u$ along $X(p)$
vanishes. -/
def SolvesTransport {n : ℕ} (X : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (u : (Fin (n + 1) → ℝ) → ℝ) : Prop :=
  ∀ p, ∑ μ : Fin (n + 1), X p μ * fderiv ℝ u p (Pi.single μ 1) = 0

/-- A curve $\gamma : \mathbb{R} \to \mathbb{R}^{n+1}$ is an integral curve of
the vector field $X$ if $\gamma'(s) = X(\gamma(s))$ for all $s$. -/
def IsIntegralCurve {n : ℕ} (X : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (γ : ℝ → (Fin (n + 1) → ℝ)) : Prop :=
  ∀ s, fderiv ℝ γ s 1 = X (γ s)

/-- **Proposition 1.0.1 (Connection between transport equations and ODEs).**
If $u$ solves the transport equation $\sum_\mu X^\mu \partial_\mu u = 0$ and
$\gamma$ is an integral curve of $X$, then $u$ is constant along $\gamma$, i.e.
$\frac{d}{ds} u(\gamma(s)) = 0$. -/
theorem transport_constant_along_chars {n : ℕ}
    (X : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (u : (Fin (n + 1) → ℝ) → ℝ)
    (γ : ℝ → (Fin (n + 1) → ℝ))
    (hu : SolvesTransport X u)
    (hγ : IsIntegralCurve X γ)
    (s : ℝ)
    (hu_diff : DifferentiableAt ℝ u (γ s))
    (hγ_diff : DifferentiableAt ℝ γ s) :
    deriv (fun s => u (γ s)) s = 0 := by

  have hchain : HasDerivAt (fun s => u (γ s)) (fderiv ℝ u (γ s) (fderiv ℝ γ s 1)) s :=
    hu_diff.hasFDerivAt.comp_hasDerivAt s hγ_diff.hasFDerivAt.hasDerivAt
  rw [hchain.deriv]

  rw [hγ s]

  have hdecomp : X (γ s) = ∑ μ : Fin (n + 1),
      (X (γ s) μ) • (Pi.single μ (1 : ℝ) : Fin (n + 1) → ℝ) := by
    ext i
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, Finset.mem_univ]
  rw [hdecomp, map_sum]
  simp only [ContinuousLinearMap.map_smul, smul_eq_mul]

  exact hu (γ s)

/-- Burger's equation $u_t + u\,u_x = 0$ in $1 + 1$ dimensions.
A function $u(t, x)$ solves Burger's equation iff the time and space partial
derivatives satisfy this nonlinear conservation law at every spacetime point. -/
def SolvesBurgers (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, deriv (fun t' => u t' x) t + u t x * deriv (fun x' => u t x') x = 0

/-- Helper: if the uncurried form of $u : \mathbb{R} \to \mathbb{R} \to \mathbb{R}$
is $C^1$, then for fixed $x$ the slice $t' \mapsto u(t', x)$ is differentiable
at $t$. -/
lemma c1_implies_t_diff
    (u : ℝ → ℝ → ℝ) (hC1 : ContDiff ℝ 1 (Function.uncurry u))
    (t x : ℝ) : DifferentiableAt ℝ (fun t' => u t' x) t :=
  ((hC1.differentiable one_ne_zero).comp
    ((differentiable_id (𝕜 := ℝ)).prodMk (differentiable_const (𝕜 := ℝ) x))).differentiableAt

/-- Helper: if the uncurried form of $u$ is $C^1$, then for fixed $t$ the
spatial slice $x' \mapsto u(t, x')$ is differentiable at $x$. -/
lemma c1_implies_x_diff
    (u : ℝ → ℝ → ℝ) (hC1 : ContDiff ℝ 1 (Function.uncurry u))
    (t x : ℝ) : DifferentiableAt ℝ (fun x' => u t x') x :=
  ((hC1.differentiable one_ne_zero).comp
    ((differentiable_const (𝕜 := ℝ) t).prodMk (differentiable_id (𝕜 := ℝ)))).differentiableAt

/-- Helper: if $u$ is jointly $C^1$, then for fixed $t$ the spatial slice
$x \mapsto u(t, x)$ is continuous. -/
lemma c1_continuous_x
    (u : ℝ → ℝ → ℝ) (hC1 : ContDiff ℝ 1 (Function.uncurry u))
    (t : ℝ) : Continuous (fun x => u t x) := by
  show Continuous ((Function.uncurry u) ∘ (fun x => (t, x)))
  exact hC1.continuous.comp (by fun_prop)

/-- The partial time-derivative of $u$ equals the joint Fréchet derivative of
the uncurried $u$ paired against the unit tangent vector $(1, 0)$. -/
lemma deriv_t_eq_fderiv_10
    (u : ℝ → ℝ → ℝ) (hC1 : ContDiff ℝ 1 (Function.uncurry u))
    (t x : ℝ) :
    deriv (fun t' => u t' x) t = fderiv ℝ (Function.uncurry u) (t, x) ((1 : ℝ), (0 : ℝ)) := by
  have hf : HasFDerivAt (Function.uncurry u) (fderiv ℝ (Function.uncurry u) (t, x)) (t, x) :=
    (hC1.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hι : HasDerivAt (fun t' => ((t' : ℝ), (x : ℝ))) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have heq : (fun t' => u t' x) = (fun t' => Function.uncurry u (t', x)) := by
    ext t'; simp [Function.uncurry]
  rw [heq]; exact (hf.comp_hasDerivAt t hι).deriv

/-- For $u$ jointly $C^1$ and fixed $t$, the map $x \mapsto u_t(t, x)$ is
continuous in the spatial variable. -/
lemma deriv_t_continuous_in_x
    (u : ℝ → ℝ → ℝ) (hC1 : ContDiff ℝ 1 (Function.uncurry u))
    (t : ℝ) : Continuous (fun x => deriv (fun t' => u t' x) t) := by
  have heq : (fun x => deriv (fun t' => u t' x) t) =
      (fun x => fderiv ℝ (Function.uncurry u) (t, x) ((1 : ℝ), (0 : ℝ))) := by
    ext x; exact deriv_t_eq_fderiv_10 u hC1 t x
  rw [heq]
  have h := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (E := ℝ × ℝ) (F := ℝ)
    (n := 0) (f := Function.uncurry u)).mp hC1
  show Continuous ((fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry u) p
    ((1 : ℝ), (0 : ℝ))) ∘ (fun x => (t, x)))
  exact ((ContinuousLinearMap.apply ℝ ℝ (1, 0)).continuous.comp
    h.2.2.continuous).comp (by fun_prop)

/-- A continuous function $f : \mathbb{R} \to \mathbb{R}$ that decays to $0$ at
both $\pm\infty$ is globally bounded: $\exists M \ge 0$ with $|f(x)| \le M$ for
all $x$. -/
lemma bounded_of_continuous_tendsto_zero
    (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_top : Filter.Tendsto f Filter.atTop (nhds 0))
    (hf_bot : Filter.Tendsto f Filter.atBot (nhds 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  have htop : ∀ᶠ x in Filter.atTop, ‖f x‖ < 1 :=
    (Metric.tendsto_nhds.mp hf_top 1 one_pos).mono (fun x hx => by rwa [dist_zero_right] at hx)
  have hbot : ∀ᶠ x in Filter.atBot, ‖f x‖ < 1 :=
    (Metric.tendsto_nhds.mp hf_bot 1 one_pos).mono (fun x hx => by rwa [dist_zero_right] at hx)
  rw [Filter.eventually_atTop] at htop
  rw [Filter.eventually_atBot] at hbot
  obtain ⟨N₁, hN₁⟩ := htop
  obtain ⟨N₂, hN₂⟩ := hbot
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf_cont.continuousOn
    (s := Set.Icc N₂ N₁)
  refine ⟨max C 1, le_max_of_le_right zero_le_one, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc N₂ N₁
  · exact (Real.norm_eq_abs (f x) ▸ hC x hx).trans (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · have := hN₂ x (le_of_lt hx)
      rw [Real.norm_eq_abs] at this; linarith [le_max_right C 1]
    · have := hN₁ x (le_of_lt hx)
      rw [Real.norm_eq_abs] at this; linarith [le_max_right C 1]

/-- A continuous, integrable function on $\mathbb{R}$ that decays to $0$ at
$\pm\infty$ has an integrable square: $f^2 \in L^1(\mathbb{R})$. -/
lemma c1_decay_implies_sq_integrable
    (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_int : Integrable f)
    (hf_top : Filter.Tendsto f Filter.atTop (nhds 0))
    (hf_bot : Filter.Tendsto f Filter.atBot (nhds 0)) :
    Integrable (fun x => f x ^ 2) := by
  obtain ⟨M, hM_pos, hM_bd⟩ := bounded_of_continuous_tendsto_zero f hf_cont hf_top hf_bot
  apply (hf_int.norm.const_mul M).mono' (hf_cont.pow 2).aestronglyMeasurable
  filter_upwards with x
  simp only [Real.norm_eq_abs]
  rw [abs_pow, sq]
  exact mul_le_mul (hM_bd x) (le_of_eq rfl) (abs_nonneg _) hM_pos

/-- Packages the hypotheses needed to apply a Leibniz / differentiation-under-the-integral
rule to $\int_{\mathbb{R}} u(t, x)^2 \, dx$: from $C^1$ regularity, spatial decay,
spatial integrability, and a uniform local bound on $\partial_t (u^2)$, derive the
exact ensemble of measurability, integrability, and pointwise differentiability
hypotheses required. -/
lemma c1_decay_implies_leibniz_hypotheses
    (u : ℝ → ℝ → ℝ) (T : ℝ)
    (_hC1 : ContDiff ℝ 1 (Function.uncurry u))
    (_hdecay : ∀ t, t ∈ Icc 0 T →
      Filter.Tendsto (fun x => u t x) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun x => u t x) Filter.atBot (nhds 0))


    (hInt_u : ∀ t, t ∈ Icc 0 T → Integrable (fun x => u t x))


    (hLeibnizBound : ∀ t', t' ∈ Icc 0 T →
      ∃ (s : Set ℝ) (_ : s ∈ nhds t') (bound : ℝ → ℝ),
        (∀ᵐ x, ∀ t'' ∈ s, ‖deriv (fun t''' => (u t''' x) ^ 2) t''‖ ≤ bound x) ∧
        Integrable bound)
    (t' : ℝ) (_ht' : t' ∈ Icc 0 T) :
    Integrable (fun x => (u t' x) ^ 2) ∧
    ∃ (s : Set ℝ) (_ : s ∈ nhds t'),
      (∀ᶠ t'' in nhds t', AEStronglyMeasurable (fun x => (u t'' x) ^ 2) volume) ∧
      AEStronglyMeasurable (fun x => deriv (fun t'' => (u t'' x) ^ 2) t') volume ∧
      ∃ (bound : ℝ → ℝ),
        (∀ᵐ x, ∀ t'' ∈ s, ‖deriv (fun t''' => (u t''' x) ^ 2) t''‖ ≤ bound x) ∧
        Integrable bound ∧
        (∀ᵐ x, ∀ t'' ∈ s, HasDerivAt (fun t''' => (u t''' x) ^ 2)
          (deriv (fun t''' => (u t''' x) ^ 2) t'') t'') := by

  have hInt : Integrable (fun x => (u t' x) ^ 2) := by
    obtain ⟨hdecay_top, hdecay_bot⟩ := _hdecay t' _ht'
    exact c1_decay_implies_sq_integrable _ (c1_continuous_x u _hC1 t')
      (hInt_u t' _ht') hdecay_top hdecay_bot

  obtain ⟨s, hs_nhd, bound, h_bound, h_bound_int⟩ := hLeibnizBound t' _ht'
  exact ⟨hInt, s, hs_nhd,

    Filter.Eventually.of_forall (fun t'' =>
      ((c1_continuous_x u _hC1 t'').pow 2).aestronglyMeasurable),


    (by
      have : Continuous (fun x => deriv (fun t'' => (u t'' x) ^ 2) t') := by
        have heq : (fun x => deriv (fun t'' => (u t'' x) ^ 2) t') =
            (fun x => 2 * u t' x * deriv (fun t'' => u t'' x) t') := by
          ext x
          have hd := c1_implies_t_diff u _hC1 t' x
          have hsq : HasDerivAt (fun t'' => (u t'' x) ^ 2)
              (2 * u t' x * deriv (fun t'' => u t'' x) t') t' := by
            have hsq' : HasDerivAt (fun t'' => u t'' x * u t'' x)
                (deriv (fun t'' => u t'' x) t' * u t' x +
                 u t' x * deriv (fun t'' => u t'' x) t') t' :=
              hd.hasDerivAt.mul hd.hasDerivAt
            have : (fun t'' => (u t'' x) ^ 2) = (fun t'' => u t'' x * u t'' x) := by ext; ring
            rw [this]; convert hsq' using 1; ring
          exact hsq.deriv
        rw [heq]
        exact (continuous_const.mul (c1_continuous_x u _hC1 t')).mul
          (deriv_t_continuous_in_x u _hC1 t')
      exact this.aestronglyMeasurable),
    bound, h_bound, h_bound_int,

    Filter.Eventually.of_forall (fun x t'' _ =>
      ((c1_implies_t_diff u _hC1 t'' x).pow 2).hasDerivAt)⟩

/-- Differentiation under the integral sign (specialised wrapper): under the
standard dominated-convergence hypotheses, the parameter integral
$t \mapsto \int_{\mathbb{R}} f(t, x) \, dx$ has derivative
$\int_{\mathbb{R}} \partial_t f(t, x) \, dx$ at $t$. -/
theorem hasDerivAt_integral
    (f : ℝ → ℝ → ℝ) (t : ℝ)
    (hf_int : Integrable (f t))

    {s : Set ℝ} (hs : s ∈ nhds t)
    (hf_meas : ∀ᶠ t' in nhds t, AEStronglyMeasurable (f t') volume)
    (hf_deriv_meas : AEStronglyMeasurable (fun x => deriv (fun t' => f t' x) t) volume)
    {bound : ℝ → ℝ}
    (h_bound : ∀ᵐ x, ∀ t' ∈ s, ‖deriv (fun t'' => f t'' x) t'‖ ≤ bound x)
    (bound_int : Integrable bound)
    (h_diff_on : ∀ᵐ x, ∀ t' ∈ s, HasDerivAt (fun t'' => f t'' x)
      (deriv (fun t'' => f t'' x) t') t') :
    HasDerivAt (fun t' => ∫ x, f t' x) (∫ x, deriv (fun t' => f t' x) t) t :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hf_meas hf_int
    hf_deriv_meas h_bound bound_int h_diff_on).2

/-- **Proposition 2.0.1 (Burger's equation is a conservation law).**
Let $u(t, x)$ be a $C^1$ solution of Burger's equation on $[0, T] \times \mathbb{R}$
that decays to $0$ as $x \to \pm \infty$ uniformly for $t \in [0, T]$ (with
suitable integrability of $u(t, \cdot)$ and a Leibniz-rule bound). Then the
spatial $L^2$ norm is conserved:
$$\int_{\mathbb{R}} u(t, x)^2 \, dx = \int_{\mathbb{R}} u(0, x)^2 \, dx
\quad \text{for all } t \in [0, T].$$ -/
theorem l2_norm_conservation_burgers
    (u : ℝ → ℝ → ℝ)
    (hu : SolvesBurgers u)
    (T : ℝ) (_hT : T ≥ 0)

    (hC1 : ContDiff ℝ 1 (Function.uncurry u))

    (hu_decay : ∀ t, t ∈ Icc 0 T →
      Filter.Tendsto (fun x => u t x) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun x => u t x) Filter.atBot (nhds 0))


    (hInt_u : ∀ t, t ∈ Icc 0 T → Integrable (fun x => u t x))


    (hLeibnizBound : ∀ t', t' ∈ Icc 0 T →
      ∃ (s : Set ℝ) (_ : s ∈ nhds t') (bound : ℝ → ℝ),
        (∀ᵐ x, ∀ t'' ∈ s, ‖deriv (fun t''' => (u t''' x) ^ 2) t''‖ ≤ bound x) ∧
        Integrable bound)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ∫ x, (u t x) ^ 2 = ∫ x, (u 0 x) ^ 2 := by

  have hu_t_diff : ∀ t x, DifferentiableAt ℝ (fun t' => u t' x) t :=
    fun t x => c1_implies_t_diff u hC1 t x
  have hu_x_diff : ∀ t x, DifferentiableAt ℝ (fun x' => u t x') x :=
    fun t x => c1_implies_x_diff u hC1 t x

  have hLeibData : ∀ t', t' ∈ Icc 0 T →
      Integrable (fun x => (u t' x) ^ 2) ∧
      ∃ (s : Set ℝ) (_ : s ∈ nhds t'),
        (∀ᶠ t'' in nhds t', AEStronglyMeasurable (fun x => (u t'' x) ^ 2) volume) ∧
        AEStronglyMeasurable (fun x => deriv (fun t'' => (u t'' x) ^ 2) t') volume ∧
        ∃ (bound : ℝ → ℝ),
          (∀ᵐ x, ∀ t'' ∈ s, ‖deriv (fun t''' => (u t''' x) ^ 2) t''‖ ≤ bound x) ∧
          Integrable bound ∧
          (∀ᵐ x, ∀ t'' ∈ s, HasDerivAt (fun t''' => (u t''' x) ^ 2)
            (deriv (fun t''' => (u t''' x) ^ 2) t'') t'') :=
    fun t' ht' => c1_decay_implies_leibniz_hypotheses u T hC1 hu_decay hInt_u hLeibnizBound t' ht'
  have hu_sq_int : ∀ t, t ∈ Icc 0 T → Integrable (fun x => (u t x) ^ 2) :=
    fun t ht => (hLeibData t ht).1


  have h_boundary_vanish : ∀ t', t' ∈ Icc 0 T →
      ∫ x, (u t' x) ^ 2 * deriv (fun x' => u t' x') x = 0 := by
    intro t' ht'
    obtain ⟨hdecay_top, hdecay_bot⟩ := hu_decay t' ht'

    have hderiv : ∀ x, HasDerivAt (fun x' => (u t' x') ^ 3 / 3)
        ((u t' x) ^ 2 * deriv (fun x' => u t' x') x) x := by
      intro x
      have h1 : HasDerivAt (fun x' => u t' x') (deriv (fun x' => u t' x') x) x :=
        (hu_x_diff t' x).hasDerivAt
      have h3 : HasDerivAt (fun x' => (u t' x') ^ 3)
          (3 * (u t' x) ^ 2 * deriv (fun x' => u t' x') x) x := by
        have hp := h1.pow 3
        simp [Nat.cast_ofNat] at hp
        exact hp
      convert (h3.div_const 3) using 1; ring

    have htop : Filter.Tendsto (fun x => (u t' x) ^ 3 / 3) Filter.atTop (nhds 0) := by
      have := (hdecay_top.pow 3).div_const 3; simp at this; exact this
    have hbot : Filter.Tendsto (fun x => (u t' x) ^ 3 / 3) Filter.atBot (nhds 0) := by
      have := (hdecay_bot.pow 3).div_const 3; simp at this; exact this

    by_cases hint : Integrable (fun x => (u t' x) ^ 2 * deriv (fun x' => u t' x') x)
    ·

      have := integral_of_hasDerivAt_of_tendsto hderiv hint hbot htop
      simp at this; exact this
    ·
      exact integral_undef hint

  have hHasDerivAt : ∀ t', t' ∈ Icc 0 T →
      HasDerivAt (fun t'' => ∫ x, (u t'' x) ^ 2) 0 t' := by
    intro t' ht'


    obtain ⟨_, s_leib, hs_leib, hf_meas_leib, hf_deriv_meas_leib, bound_leib,
        h_bound_leib, bound_int_leib, h_diff_on_leib⟩ := hLeibData t' ht'
    have hLeib := hasDerivAt_integral (fun t'' x => (u t'' x) ^ 2) t'
        (hu_sq_int t' ht') hs_leib hf_meas_leib hf_deriv_meas_leib
        h_bound_leib bound_int_leib h_diff_on_leib

    suffices hval : (∫ x, deriv (fun t'' => (u t'' x) ^ 2) t') = 0 by
      rwa [hval] at hLeib

    have hpw : ∀ x, deriv (fun t'' => (u t'' x) ^ 2) t' =
        -(2 * (u t' x) ^ 2 * deriv (fun x' => u t' x') x) := by
      intro x

      have hf := hu_t_diff t' x
      have hd : HasDerivAt (fun t'' => (u t'' x) ^ 2)
          (2 * u t' x * deriv (fun t'' => u t'' x) t') t' := by
        have hsq : HasDerivAt (fun t'' => u t'' x * u t'' x)
            (deriv (fun t'' => u t'' x) t' * u t' x + u t' x * deriv (fun t'' => u t'' x) t') t' :=
          hf.hasDerivAt.mul hf.hasDerivAt
        have heq : (fun t'' => (u t'' x) ^ 2) = (fun t'' => u t'' x * u t'' x) := by
          ext t''; ring
        rw [heq]
        convert hsq using 1; ring
      rw [hd.deriv]
      have hburg : deriv (fun t'' => u t'' x) t' =
          -(u t' x * deriv (fun x' => u t' x') x) := by linarith [hu t' x]
      rw [hburg]; ring
    simp_rw [hpw]
    rw [show (fun x => -(2 * (u t' x) ^ 2 * deriv (fun x' => u t' x') x))
        = (fun x => (-2) * ((u t' x) ^ 2 * deriv (fun x' => u t' x') x)) from by ext; ring]
    rw [integral_const_mul, h_boundary_vanish t' ht', mul_zero]


  have hcont : ContinuousOn (fun t' => ∫ x, (u t' x) ^ 2) (Icc 0 T) :=
    fun t' ht' => (hHasDerivAt t' ht').continuousAt.continuousWithinAt
  apply constant_of_has_deriv_right_zero hcont
  · intro t' ht'
    exact (hHasDerivAt t' (Ico_subset_Icc_self ht')).hasDerivWithinAt
  · exact ht

end TransportBurgers

namespace TransportBurgers.Characteristics

open TransportBurgers


/-- **Definition 2.0.1 (Characteristic curves).** A characteristic curve for
Burger's equation with solution $u$ is a pair $(\gamma_t, \gamma_x) : \mathbb{R} \to
\mathbb{R}^2$ satisfying the ODE system
$$\frac{d}{ds} \gamma_t(s) = 1, \qquad
\frac{d}{ds} \gamma_x(s) = u(\gamma_t(s), \gamma_x(s)).$$ -/
structure BurgersCharacteristic (u : ℝ → ℝ → ℝ) (γ_t γ_x : ℝ → ℝ) : Prop where
  time_param : ∀ s, deriv γ_t s = 1
  space_param : ∀ s, deriv γ_x s = u (γ_t s) (γ_x s)

/-- **Proposition 2.0.3 (Burger characteristics are straight lines).**
Given a characteristic $(\gamma_t, \gamma_x)$ for Burger's equation along which
$u$ is constant, the spatial component is a straight line:
$\gamma_x(s) = \gamma_x(0) + u(\gamma_t(0), \gamma_x(0)) \cdot s$. -/
theorem burgers_chars_straight_lines
    (u : ℝ → ℝ → ℝ) (γ_t γ_x : ℝ → ℝ)
    (_hu : SolvesBurgers u) (hchar : BurgersCharacteristic u γ_t γ_x)
    (hconst : ∀ s, u (γ_t s) (γ_x s) = u (γ_t 0) (γ_x 0))
    (_ht_init : γ_t 0 = 0)
    (hx_diff : Differentiable ℝ γ_x) :
    ∀ s, γ_x s = γ_x 0 + u (γ_t 0) (γ_x 0) * s := by
  set c := u (γ_t 0) (γ_x 0)

  have hderiv_const : ∀ s, deriv γ_x s = c := by
    intro s
    rw [hchar.space_param s, hconst s]

  have hh_deriv : ∀ s, deriv (fun s => γ_x s - c * s) s = 0 := by
    intro s
    have h1 : HasDerivAt γ_x c s := by
      rw [← hderiv_const s]; exact (hx_diff s).hasDerivAt
    have h2 : HasDerivAt (fun s => c * s) c s := by
      simpa using (hasDerivAt_id s).const_mul c
    exact (h1.sub h2).deriv.trans (sub_self c)
  have hh_diff : Differentiable ℝ (fun s => γ_x s - c * s) :=
    hx_diff.sub (differentiable_const c |>.mul differentiable_id)

  have hh_const := is_const_of_deriv_eq_zero hh_diff hh_deriv
  intro s
  have := hh_const s 0
  simp at this
  linarith

/-- The time component of a Burger's characteristic has zero acceleration:
$\gamma_t''(s) = 0$ for all $s$ (a direct consequence of $\gamma_t'(s) = 1$). -/
theorem burgers_char_zero_accel_time
    (u : ℝ → ℝ → ℝ) (γ_t γ_x : ℝ → ℝ)
    (hchar : BurgersCharacteristic u γ_t γ_x) :
    ∀ s, deriv (deriv γ_t) s = 0 := by
  intro s
  have : deriv γ_t = fun _ => (1 : ℝ) := funext hchar.time_param
  rw [this]
  exact deriv_const s 1

/-- The spatial component of a Burger's characteristic has zero acceleration:
if $u$ is constant along the characteristic, then $\gamma_x''(s) = 0$. -/
theorem burgers_char_zero_accel_space
    (u : ℝ → ℝ → ℝ) (γ_t γ_x : ℝ → ℝ)
    (hchar : BurgersCharacteristic u γ_t γ_x)
    (hconst : ∀ s, deriv (fun s => u (γ_t s) (γ_x s)) s = 0)
    (hx_diff : Differentiable ℝ γ_x) :
    ∀ s, deriv (deriv γ_x) s = 0 := by
  intro s
  have hderiv_eq : deriv γ_x = fun s => u (γ_t s) (γ_x s) := by
    ext s'
    have h1 : HasDerivAt γ_x (u (γ_t s') (γ_x s')) s' := by
      rw [← hchar.space_param s']
      exact (hx_diff s').hasDerivAt
    exact h1.deriv
  rw [hderiv_eq]
  exact hconst s

end TransportBurgers.Characteristics
