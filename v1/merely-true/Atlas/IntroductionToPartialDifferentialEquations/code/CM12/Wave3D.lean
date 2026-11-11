/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Atlas.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D

set_option maxHeartbeats 3200000

noncomputable section

open Matrix Real MeasureTheory Filter intervalIntegral

namespace WaveEquation3D

/-- Shorthand for $3$-dimensional Euclidean space $\mathbb{R}^3$ used as the
spatial domain for the wave equation. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Predicate stating that $u : \mathbb{R} \times \mathbb{R}^3 \to \mathbb{R}$
is a $C^2$ solution of the $3$-dimensional wave equation
$-\partial_t^2 u + \Delta u = 0$. -/
structure IsWaveSolution3D (u : ℝ → E3 → ℝ) : Prop where
  smooth : ContDiff ℝ 2 (fun p : ℝ × E3 => u p.1 p.2)
  wave_eq : ∀ t : ℝ, ∀ x : E3,
    fderiv ℝ (fun s => fderiv ℝ (fun s' => u s' x) s 1) t 1 =
    ∑ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ (fun y' => u t y') y (EuclideanSpace.single i 1))
        x (EuclideanSpace.single i 1)

/-- Cauchy data for the $3$D wave equation: an initial position $f \in C^3(\mathbb{R}^3)$
and an initial velocity $g \in C^2(\mathbb{R}^3)$. -/
structure CauchyData3D where
  f : E3 → ℝ
  g : E3 → ℝ
  f_smooth : ContDiff ℝ 3 f
  g_smooth : ContDiff ℝ 2 g

/-- Conversion from spherical coordinates $(\theta, \varphi)$ on the unit sphere $S^2 \subset \mathbb{R}^3$
to Cartesian coordinates $(\sin\theta\cos\varphi, \sin\theta\sin\varphi, \cos\theta)$. -/
def sphericalToCart (θ φ : ℝ) : E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![sin θ * cos φ, sin θ * sin φ, cos θ]

/-- The spherical mean of $h : \mathbb{R}^3 \to \mathbb{R}$ over the sphere
$\partial B_r(x)$ of radius $r$ centred at $x$, defined via the spherical
parametrization
$\frac{1}{4\pi}\int_0^\pi\!\!\int_0^{2\pi} h(x + r\,\omega(\theta,\varphi))\sin\theta\,d\varphi\,d\theta$. -/
noncomputable def SphericalMean (h : E3 → ℝ) (x : E3) (r : ℝ) : ℝ :=
  (1 / (4 * π)) *
    ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
      h (x + r • sphericalToCart θ φ) * sin θ

/-- Elementary computation: $\int_0^\pi \sin\theta\, d\theta = 2$. -/
lemma integral_sin_eq_two : ∫ θ in (0 : ℝ)..π, sin θ = 2 := by
  rw [integral_sin]; simp [Real.cos_pi, Real.cos_zero]; ring

/-- The spherical mean over a sphere of radius zero equals the value at the
centre: $\mathrm{SphericalMean}\,h\,x\,0 = h(x)$. -/
lemma sphericalMean_at_zero (h : E3 → ℝ) (x : E3) : SphericalMean h x 0 = h x := by
  unfold SphericalMean; simp only [zero_smul, add_zero]
  simp_rw [show ∀ (θ : ℝ), ∫ φ in (0 : ℝ)..(2 * π), h x * sin θ =
    h x * sin θ * (2 * π) from fun θ => by
      rw [intervalIntegral.integral_const]; simp [smul_eq_mul]; ring]
  rw [show (fun θ => h x * sin θ * (2 * π)) = (fun θ => h x * (2 * π) * sin θ) from by ext; ring]
  rw [intervalIntegral.integral_const_mul, integral_sin_eq_two]
  have hpi : (4 : ℝ) * π ≠ 0 := by positivity
  field_simp; ring

/-- The spherical-to-Cartesian map (viewed as a function of an outer parameter and
the angles $(\theta, \varphi)$) is continuous. -/
lemma sphericalToCart_continuous : Continuous (fun p : (ℝ × ℝ) × ℝ =>
    (EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![sin p.1.2 * cos p.2, sin p.1.2 * sin p.2, cos p.1.2]) := by
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact (continuous_sin.comp (continuous_snd.comp continuous_fst)).mul
      (continuous_cos.comp continuous_snd)
  · exact (continuous_sin.comp (continuous_snd.comp continuous_fst)).mul
      (continuous_sin.comp continuous_snd)
  · exact continuous_cos.comp (continuous_snd.comp continuous_fst)

/-- If $h$ is continuous, then $r \mapsto \mathrm{SphericalMean}\,h\,x\,r$ is
continuous in the radius $r$. -/
lemma sphericalMean_continuous (h : E3 → ℝ) (hh : Continuous h) (x : E3) :
    Continuous (fun r => SphericalMean h x r) := by
  unfold SphericalMean
  apply Continuous.const_mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
  apply Continuous.mul
  · exact hh.comp (continuous_const.add ((continuous_fst.comp continuous_fst).smul
      sphericalToCart_continuous))
  · exact continuous_sin.comp (continuous_snd.comp continuous_fst)

/-- Definitional unfolding of `SphericalMean` as a parametric integral in spherical
coordinates. Used to expose the integral form after the definition is marked irreducible. -/
lemma SphericalMean_eq (h : E3 → ℝ) (x : E3) (r : ℝ) :
    SphericalMean h x r = (1 / (4 * π)) *
      ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
        h (x + r • sphericalToCart θ φ) * sin θ := rfl


attribute [irreducible] SphericalMean

/-- The surface integral $\int_{\partial B_r(x)} h\,d\sigma = 4\pi r^2 \cdot \mathrm{SphericalMean}\,h\,x\,r$
on the sphere of radius $r$ around $x$. -/
noncomputable def SphereIntegral (h : E3 → ℝ) (x : E3) (r : ℝ) : ℝ :=
  4 * π * r ^ 2 * SphericalMean h x r

/-- The integral over $\partial B_r(x)$ of the radial (outward normal) derivative of $h$,
expressed as $4\pi r^2$ times the radial derivative of the spherical mean. -/
noncomputable def SphereIntegralNormalDeriv (h : E3 → ℝ) (x : E3) (r : ℝ) : ℝ :=
  4 * π * r ^ 2 * deriv (fun ρ => SphericalMean h x ρ) r










/-- Product-rule identity: for $f \in C^2$,
$\frac{d^2}{d\rho^2}(\rho f(\rho))\big|_{\rho = x} = x f''(x) + 2 f'(x)$. -/
lemma iteratedDeriv_two_mul_id (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : ℝ) :
    iteratedDeriv 2 (fun ρ => ρ * f ρ) x = x * iteratedDeriv 2 f x + 2 * deriv f x := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hf' : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hf'' : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two

  have h1 : ∀ y, HasDerivAt (fun ρ => ρ * f ρ) (f y + y * deriv f y) y := by
    intro y
    have h := (hasDerivAt_id y).mul (hf'.differentiableAt.hasDerivAt)
    convert h using 1; simp
  have h1_eq : ∀ y, deriv (fun ρ => ρ * f ρ) y = f y + y * deriv f y :=
    fun y => (h1 y).deriv

  have h2 : HasDerivAt (fun y => f y + y * deriv f y)
      (deriv f x + (deriv f x + x * deriv (deriv f) x)) x := by
    exact (hf'.differentiableAt.hasDerivAt).add (by
      have h := (hasDerivAt_id x).mul (hf''.differentiableAt.hasDerivAt)
      convert h using 1; simp)
  have : deriv (deriv fun ρ => ρ * f ρ) x = deriv (fun y => f y + y * deriv f y) x := by
    congr 1; exact funext h1_eq
  rw [this, h2.deriv]; ring












/-- For a continuous $h$, the spherical mean tends to the centre value as the radius
shrinks to $0^+$: $\lim_{r \to 0^+} \mathrm{SphericalMean}\,h\,x\,r = h(x)$. -/
theorem sphericalMean_limit_zero (h : E3 → ℝ) (hh : Continuous h) (x : E3) :
    Tendsto (fun r => SphericalMean h x r) (nhdsWithin 0 (Set.Ioi 0)) (nhds (h x)) := by
  rw [← sphericalMean_at_zero h x]
  exact ((sphericalMean_continuous h hh x).continuousAt).continuousWithinAt.tendsto


/-- The "tilde" initial position: $\tilde F(r, x) := r \cdot \mathrm{SphericalMean}(f)(x, r)$,
the spatial profile of the auxiliary $1+1$-dimensional wave problem associated with $u$. -/
def F_tilde (data : CauchyData3D) (r : ℝ) (x : E3) : ℝ :=
  r * SphericalMean data.f x r

/-- The "tilde" initial velocity: $\tilde G(r, x) := r \cdot \mathrm{SphericalMean}(g)(x, r)$. -/
def G_tilde (data : CauchyData3D) (r : ℝ) (x : E3) : ℝ :=
  r * SphericalMean data.g x r

/-- The surface integral equals the area of the sphere times the spherical mean:
$\int_{\partial B_r(x)} h\,d\sigma = 4\pi r^2 \cdot \mathrm{SphericalMean}\,h\,x\,r$. -/
theorem sphere_integral_eq_area_times_mean
    (h : E3 → ℝ) (x : E3) (r : ℝ) :
    SphereIntegral h x r = 4 * π * r ^ 2 * SphericalMean h x r := by
  rfl

/-- The integral of the outward normal derivative is $4\pi t^2$ times the radial derivative
of the spherical mean. -/
theorem sphericalMean_normal_deriv_relation
    (f : E3 → ℝ) (x : E3) (t : ℝ) (_ht : 0 < t) :
    SphereIntegralNormalDeriv f x t =
      4 * π * t ^ 2 * deriv (fun r => SphericalMean f x r) t := by
  rfl


/-- The symmetric difference quotient $(f(t+h) - f(t-h))/(2h)$ tends to the derivative
$f'(t)$ as $h \to 0^+$, provided $f$ has a derivative $d$ at $t$. -/
theorem symmetric_derivative_tendsto (f : ℝ → ℝ) (t d : ℝ) (hf : HasDerivAt f d t) :
    Tendsto (fun h => (f (t + h) - f (t - h)) / (2 * h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d) := by

  have hfwd : Tendsto (fun h => h⁻¹ • (f (t + h) - f t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d) :=
    hf.tendsto_slope_zero_right

  have hbwd_left : Tendsto (fun s => s⁻¹ • (f (t + s) - f t))
      (nhdsWithin 0 (Set.Iio 0)) (nhds d) :=
    hf.tendsto_slope_zero_left

  have hmap : Tendsto (fun h : ℝ => -h) (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhdsWithin 0 (Set.Iio 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (by simpa using continuous_neg.tendsto (0 : ℝ) :
        Tendsto (fun h : ℝ => -h) (nhds 0) (nhds 0)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      simp [Set.mem_Iio, hh]

  have hbwd : Tendsto (fun h => (-h)⁻¹ • (f (t + (-h)) - f t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d) :=
    hbwd_left.comp hmap

  have hbwd' : Tendsto (fun h => h⁻¹ • (f t - f (t - h)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d) := by
    have : (fun h => h⁻¹ • (f t - f (t - h))) =
        (fun h => (-h)⁻¹ • (f (t + (-h)) - f t)) := by
      ext h; simp [inv_neg, smul_eq_mul, sub_eq_add_neg]; ring
    rw [this]; exact hbwd

  have hsum : Tendsto (fun h => h⁻¹ • (f (t + h) - f t) + h⁻¹ • (f t - f (t - h)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (d + d)) :=
    hfwd.add hbwd'

  have hdiv : Tendsto (fun h => (h⁻¹ • (f (t + h) - f t) + h⁻¹ • (f t - f (t - h))) / 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((d + d) / 2)) :=
    hsum.div_const 2
  rw [show (d + d) / 2 = d from by ring] at hdiv

  exact hdiv.congr (fun h => by
    simp [smul_eq_mul]
    by_cases hh : h = 0
    · simp [hh]
    · field_simp; ring)

/-- For a continuous $g$, the integral average over a shrinking symmetric interval
$\frac{1}{2h}\int_{t-h}^{t+h} g(\rho)\,d\rho$ tends to $g(t)$ as $h \to 0^+$. -/
theorem integral_average_tendsto (g : ℝ → ℝ) (t : ℝ) (hg : Continuous g) :
    Tendsto (fun h => (∫ ρ in (t - h)..(h + t), g ρ) / (2 * h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g t)) := by

  let G : ℝ → ℝ := fun u => ∫ x in t..u, g x

  have hG : HasDerivAt G (g t) t :=
    integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

  have heqf : (fun h => (∫ ρ in (t - h)..(h + t), g ρ) / (2 * h)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun h => (G (t + h) - G (t - h)) / (2 * h)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    congr 1
    show (∫ ρ in (t - h)..(h + t), g ρ) = G (t + h) - G (t - h)
    have h1 : IntervalIntegrable g volume (t - h) t := hg.intervalIntegrable _ _
    have h2 : IntervalIntegrable g volume t (t + h) := hg.intervalIntegrable _ _
    rw [show h + t = t + h from by ring]
    rw [← integral_add_adjacent_intervals h1 h2]
    rw [integral_symm t (t - h)]
    ring
  rw [Filter.tendsto_congr' heqf]
  exact symmetric_derivative_tendsto G t (g t) hG

/-- The spherical-to-Cartesian map $(\theta, \varphi) \mapsto \omega(\theta, \varphi)$
is $C^\infty$ smooth. -/
lemma contDiff_sphericalToCart_pair :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => sphericalToCart p.1 p.2) := by
  unfold sphericalToCart
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact (contDiff_sin.comp contDiff_fst).mul (contDiff_cos.comp contDiff_snd)
  · exact (contDiff_sin.comp contDiff_fst).mul (contDiff_sin.comp contDiff_snd)
  · exact contDiff_cos.comp contDiff_fst









/-- $\tilde G(t, x) = \frac{1}{4\pi t}\int_{\partial B_t(x)} g\,d\sigma$, the
last term of Kirchhoff's formula. -/
theorem G_tilde_equals_sphere_integral
    (data : CauchyData3D) (t : ℝ) (ht : 0 < t) (x : E3) :
    G_tilde data t x = (1 / (4 * π * t)) * SphereIntegral data.g x t := by
  unfold G_tilde
  rw [sphere_integral_eq_area_times_mean]
  have hpi : (π : ℝ) ≠ 0 := pi_ne_zero
  have ht' : (t : ℝ) ≠ 0 := ne_of_gt ht
  field_simp


/-- The spherical average $\mathrm{SphericalMean}(u(t,\cdot))(x, r)$ of a wave solution
$u$ at time $t$, centred at $x$ with radius $r$. -/
def sphericalAverage (u : ℝ → E3 → ℝ) (t r : ℝ) (x : E3) : ℝ :=
  SphericalMean (u t) x r

/-- The radius-weighted spherical average $r \cdot \mathrm{SphericalMean}(u(t,\cdot))(x, r)$,
which solves a $1+1$-dimensional half-line wave equation in $(t, r)$. -/
def sphericalAverage_tilde (u : ℝ → E3 → ℝ) (t r : ℝ) (x : E3) : ℝ :=
  r * sphericalAverage u t r x


/-- Initial position of the weighted spherical average: $\tilde A(0, r, x) = \tilde F(r, x)$. -/
theorem sphericalAverage_tilde_initial_position
    (data : CauchyData3D) (u : ℝ → E3 → ℝ)
    (_hu : IsWaveSolution3D u)
    (hf : ∀ x, u 0 x = data.f x)
    (_hg : ∀ x, fderiv ℝ (fun t => u t x) 0 1 = data.g x)
    (r : ℝ) (_hr : 0 < r) (x : E3) :
    sphericalAverage_tilde u 0 r x = F_tilde data r x := by
  unfold sphericalAverage_tilde sphericalAverage F_tilde
  congr 1
  congr 1
  ext y
  exact hf y







/-- The Minkowski metric $m_{\mu\nu} = \mathrm{diag}(-1, 1, \dots, 1)$ on $\mathbb{R}^{1+n}$
as a matrix indexed by `Fin (n + 1)`. -/
def minkowskiMetric (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => if i = j then (if (i : ℕ) = 0 then -1 else 1) else 0

/-- The Minkowski inner product $m(X, Y) = X^\alpha m_{\alpha\beta} Y^\beta$
on $\mathbb{R}^{1+n}$. -/
def minkowskiInner (n : ℕ) (X Y : Fin (n + 1) → ℝ) : ℝ :=
  dotProduct X (minkowskiMetric n *ᵥ Y)

/-- The Minkowski inner product is symmetric: $m(X, Y) = m(Y, X)$. -/
theorem minkowskiInner_comm (n : ℕ) (X Y : Fin (n + 1) → ℝ) :
    minkowskiInner n X Y = minkowskiInner n Y X := by
  simp only [minkowskiInner, minkowskiMetric, dotProduct, mulVec, of_apply]
  simp [mul_comm]

/-- A vector $X \in \mathbb{R}^{1+n}$ is **timelike** if $m(X, X) < 0$
(Definition 2.0.1, case (1)). -/
def IsTimelike (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X < 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is **spacelike** if $m(X, X) > 0$
(Definition 2.0.1, case (2)). -/
def IsSpacelike (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X > 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is **null** if $m(X, X) = 0$
(Definition 2.0.1, case (3)). -/
def IsNull (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X = 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is **causal** if it is timelike or null,
equivalently $m(X, X) \le 0$ (Definition 2.0.1, case (4)). -/
def IsCausal (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X ≤ 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is **future-directed** if its time component
satisfies $X^0 > 0$ (Definition 2.0.2). -/
def IsFutureDirected (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  X 0 > 0

/-- A matrix $\Lambda$ is a **Lorentz transformation** if it preserves the Minkowski
metric: $\Lambda^T m \Lambda = m$ (Definition 2.1.1). -/
def IsLorentzTransformation (n : ℕ) (Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  Λᵀ * minkowskiMetric n * Λ = minkowskiMetric n

/-- A Lorentz transformation preserves the Minkowski inner product:
$m(\Lambda X, \Lambda Y) = m(X, Y)$. -/
theorem lorentz_preserves_inner {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    (X Y : Fin (n + 1) → ℝ) :
    minkowskiInner n (Λ *ᵥ X) (Λ *ᵥ Y) = minkowskiInner n X Y := by
  simp only [minkowskiInner]


  rw [mulVec_mulVec]


  rw [dotProduct_mulVec (Λ *ᵥ X) (minkowskiMetric n * Λ) Y]


  rw [vecMul_mulVec Λ (minkowskiMetric n * Λ) X]


  rw [← Matrix.mul_assoc, hΛ]

  rw [← dotProduct_mulVec]

/-- Corollary 2.1.1 (timelike case): Lorentz transformations preserve timelike vectors. -/
theorem lorentz_preserves_timelike {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    {X : Fin (n + 1) → ℝ}
    (hX : IsTimelike n X) :
    IsTimelike n (Λ *ᵥ X) := by
  unfold IsTimelike at *
  rw [lorentz_preserves_inner hΛ]
  exact hX

/-- Corollary 2.1.1 (spacelike case): Lorentz transformations preserve spacelike vectors. -/
theorem lorentz_preserves_spacelike {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    {X : Fin (n + 1) → ℝ}
    (hX : IsSpacelike n X) :
    IsSpacelike n (Λ *ᵥ X) := by
  unfold IsSpacelike at *
  rw [lorentz_preserves_inner hΛ]
  exact hX

/-- Corollary 2.1.1 (null case): Lorentz transformations preserve null vectors. -/
theorem lorentz_preserves_null {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    {X : Fin (n + 1) → ℝ}
    (hX : IsNull n X) :
    IsNull n (Λ *ᵥ X) := by
  unfold IsNull at *
  rw [lorentz_preserves_inner hΛ]
  exact hX

/-- Corollary 2.1.1 (causal case): Lorentz transformations preserve causal vectors. -/
theorem lorentz_preserves_causal {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    {X : Fin (n + 1) → ℝ}
    (hX : IsCausal n X) :
    IsCausal n (Λ *ᵥ X) := by
  unfold IsCausal at *
  rw [lorentz_preserves_inner hΛ]
  exact hX

/-- A **null frame** on $\mathbb{R}^{1+n}$ (Definition 2.2.1):
a basis $\{L, \underline L, e_{(1)}, \dots, e_{(n-1)}\}$ where $L, \underline L$ are null
with $m(L, \underline L) = -2$, and the $e_{(i)}$ are $m$-orthonormal vectors $m$-orthogonal
to both $L$ and $\underline L$. The `completeness` field records the resulting expansion
$X = -\tfrac12 m(\underline L, X) L - \tfrac12 m(L, X)\underline L + \sum_i m(e_{(i)}, X) e_{(i)}$. -/
structure NullFrame (n : ℕ) where
  L : Fin (n + 1) → ℝ
  Lb : Fin (n + 1) → ℝ
  e : Fin (n - 1) → (Fin (n + 1) → ℝ)
  L_null : minkowskiInner n L L = 0
  Lb_null : minkowskiInner n Lb Lb = 0
  L_Lb_inner : minkowskiInner n L Lb = -2
  e_orthonormal : ∀ i j : Fin (n - 1),
    minkowskiInner n (e i) (e j) = if i = j then 1 else 0
  L_e_orthog : ∀ i : Fin (n - 1), minkowskiInner n L (e i) = 0
  Lb_e_orthog : ∀ i : Fin (n - 1), minkowskiInner n Lb (e i) = 0
  completeness : ∀ X : Fin (n + 1) → ℝ,
    X = (-(1/2) * minkowskiInner n Lb X) • L
      + (-(1/2) * minkowskiInner n L X) • Lb
      + ∑ i, (minkowskiInner n (e i) X) • (e i)

/-- The **angular metric** $h(X, Y) := \sum_i m(e_{(i)}, X) m(e_{(i)}, Y)$ associated
with a null frame; it is positive-definite on the $m$-orthogonal complement of
$\mathrm{span}(L, \underline L)$ and vanishes on $\mathrm{span}(L, \underline L)$. -/
def angularMetric (n : ℕ) (nf : NullFrame n) (X Y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n - 1), minkowskiInner n (nf.e i) X * minkowskiInner n (nf.e i) Y

/-- **Proposition 2.2.1** (null-frame decomposition of $m$):
$m(X, Y) = -\tfrac12 m(L, X) m(\underline L, Y) - \tfrac12 m(\underline L, X) m(L, Y) + h(X, Y)$
where $h$ is the angular metric of the null frame. -/
theorem nullFrame_decomposition {n : ℕ} (nf : NullFrame n)
    (X Y : Fin (n + 1) → ℝ) :
    minkowskiInner n X Y =
      -(1 / 2) * minkowskiInner n nf.L X * minkowskiInner n nf.Lb Y
      - (1 / 2) * minkowskiInner n nf.Lb X * minkowskiInner n nf.L Y
      + angularMetric n nf X Y := by
  conv_lhs => rw [nf.completeness X]
  simp only [minkowskiInner, angularMetric]
  rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct]
  rw [sum_dotProduct (Finset.univ)
    (fun i => (dotProduct (nf.e i) (minkowskiMetric n *ᵥ X)) • nf.e i)]
  simp only [smul_dotProduct, smul_eq_mul]
  ring

/-- The angular metric vanishes on $L$ in the first argument: $h(L, Y) = 0$. -/
theorem angularMetric_vanish_L {n : ℕ} (nf : NullFrame n) (Y : Fin (n + 1) → ℝ) :
    angularMetric n nf nf.L Y = 0 := by
  simp only [angularMetric]
  apply Finset.sum_eq_zero
  intro i _
  have h : minkowskiInner n (nf.e i) nf.L = 0 := by
    rw [minkowskiInner_comm]; exact nf.L_e_orthog i
  simp [h]

/-- The angular metric vanishes on $\underline L$ in the first argument: $h(\underline L, Y) = 0$. -/
theorem angularMetric_vanish_Lb {n : ℕ} (nf : NullFrame n) (Y : Fin (n + 1) → ℝ) :
    angularMetric n nf nf.Lb Y = 0 := by
  simp only [angularMetric]
  apply Finset.sum_eq_zero
  intro i _
  have h : minkowskiInner n (nf.e i) nf.Lb = 0 := by
    rw [minkowskiInner_comm]; exact nf.Lb_e_orthog i
  simp [h]

/-- The angular metric is symmetric: $h(X, Y) = h(Y, X)$. -/
theorem angularMetric_comm {n : ℕ} (nf : NullFrame n) (X Y : Fin (n + 1) → ℝ) :
    angularMetric n nf X Y = angularMetric n nf Y X := by
  simp only [angularMetric]
  congr 1; ext i; ring

/-- The angular metric vanishes on $L$ in the second argument: $h(X, L) = 0$. -/
theorem angularMetric_vanish_L_right {n : ℕ} (nf : NullFrame n) (X : Fin (n + 1) → ℝ) :
    angularMetric n nf X nf.L = 0 := by
  rw [angularMetric_comm]; exact angularMetric_vanish_L nf X

/-- The angular metric vanishes on $\underline L$ in the second argument: $h(X, \underline L) = 0$. -/
theorem angularMetric_vanish_Lb_right {n : ℕ} (nf : NullFrame n) (X : Fin (n + 1) → ℝ) :
    angularMetric n nf X nf.Lb = 0 := by
  rw [angularMetric_comm]; exact angularMetric_vanish_Lb nf X

/-- Values of the angular metric on the angular basis: $h(e_{(i)}, e_{(j)}) = \delta_{ij}$. -/
theorem angularMetric_on_e {n : ℕ} (nf : NullFrame n) (i j : Fin (n - 1)) :
    angularMetric n nf (nf.e i) (nf.e j) = if i = j then 1 else 0 := by
  simp only [angularMetric, nf.e_orthonormal]
  by_cases h : i = j
  · subst h
    simp [Finset.sum_ite_eq']
  · simp only [h, ite_false]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i <;> by_cases hkj : k = j
    · subst hki; subst hkj; exact absurd rfl h
    · subst hki; simp [h]
    · simp [hki]
    · simp [hki]

/-- The angular metric is positive semidefinite: $h(X, X) \ge 0$. -/
theorem angularMetric_nonneg {n : ℕ} (nf : NullFrame n) (X : Fin (n + 1) → ℝ) :
    0 ≤ angularMetric n nf X X := by
  simp only [angularMetric]
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg _

/-- The angular metric is positive-definite on the $m$-orthogonal complement of
$\mathrm{span}(L, \underline L)$: if $X \ne 0$ with $m(L, X) = m(\underline L, X) = 0$,
then $h(X, X) > 0$. -/
theorem angularMetric_pos_def {n : ℕ} (nf : NullFrame n)
    (X : Fin (n + 1) → ℝ) (hL : minkowskiInner n nf.L X = 0)
    (hLb : minkowskiInner n nf.Lb X = 0) (hX : X ≠ 0) :
    0 < angularMetric n nf X X := by
  simp only [angularMetric]
  apply Finset.sum_pos'
  · intro i _; exact mul_self_nonneg _
  · by_contra h_none
    push Not at h_none
    apply hX
    have h_zero : ∀ i : Fin (n - 1), minkowskiInner n (nf.e i) X = 0 := by
      intro i
      have h1 := h_none i (Finset.mem_univ i)
      have h2 := mul_self_nonneg (minkowskiInner n (nf.e i) X)
      exact mul_self_eq_zero.mp (le_antisymm h1 h2)
    have := nf.completeness X
    rw [hLb, hL] at this
    simp only [mul_zero, zero_smul, zero_add] at this
    rw [this]
    simp only [h_zero, zero_smul, Finset.sum_const_zero]

/-- The Minkowski metric is an involution: $m \cdot m = I$. -/
theorem minkowskiMetric_sq (n : ℕ) : minkowskiMetric n * minkowskiMetric n = 1 := by
  ext i j
  simp only [minkowskiMetric, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hij : i = j
  · subst hij; by_cases hi : (i : ℕ) = 0 <;> simp [hi]
  · by_cases hj : (j : ℕ) = 0 <;> simp [hij, hj]

/-- The Minkowski metric is its own inverse: $m^{-1} = m$. -/
theorem minkowskiMetric_inv (n : ℕ) : (minkowskiMetric n)⁻¹ = minkowskiMetric n :=
  inv_eq_left_inv (minkowskiMetric_sq n)

/-- "Index-raising cancellation": $m(V, m \cdot W) = V \cdot W$ (Euclidean dot product). -/
theorem minkowskiInner_eta_cancel (n : ℕ) (V W : Fin (n + 1) → ℝ) :
    minkowskiInner n V (minkowskiMetric n *ᵥ W) = dotProduct V W := by
  simp only [minkowskiInner, mulVec_mulVec, minkowskiMetric_sq, one_mulVec]

/-- **Proposition 2.2.1** (raised-index version): the inverse Minkowski metric admits
the null-frame decomposition
$(m^{-1})^{\mu\nu} = -\tfrac12 L^\mu \underline L^\nu - \tfrac12 \underline L^\mu L^\nu + \sum_i e_{(i)}^\mu e_{(i)}^\nu$. -/
theorem nullFrame_inverse_decomposition {n : ℕ} (nf : NullFrame n)
    (μ ν : Fin (n + 1)) :
    (minkowskiMetric n)⁻¹ μ ν =
      -(1 / 2) * nf.L μ * nf.Lb ν
      - (1 / 2) * nf.Lb μ * nf.L ν
      + ∑ i : Fin (n - 1), nf.e i μ * nf.e i ν := by

  rw [minkowskiMetric_inv]

  have h_entry : minkowskiMetric n μ ν = (minkowskiMetric n *ᵥ Pi.single ν 1) μ := by
    simp [mulVec, dotProduct, minkowskiMetric, Matrix.of_apply, Pi.single_apply]
  rw [h_entry]

  have h_comp := nf.completeness (minkowskiMetric n *ᵥ Pi.single ν 1)

  have h_μ := congr_fun h_comp μ
  rw [h_μ]

  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    minkowskiInner_eta_cancel,
    dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

  congr 1
  · ring
  · congr 1; ext i; ring

end WaveEquation3D
