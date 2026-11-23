/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions
open Real Set MeasureTheory

noncomputable section

namespace CM8

/-- The Newtonian-potential convolution in $\mathbb{R}^3$: given $f : \mathbb{R}^3 \to \mathbb{R}$,
`phiConvolution f x` is $\int_{\mathbb{R}^3} \Phi(x - y) f(y) \, d^3 y$, where $\Phi$ is the
3D fundamental solution of the Laplacian. -/
def phiConvolution (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∫ y : Fin 3 → ℝ, Phi3 (x - y) * f y

/-- The Laplacian $\Delta f = \sum_{i=1}^{3} \partial_i^2 f$ on $\mathbb{R}^3$, specialised from
the general `laplacian` to dimension three. -/
def laplacian3 (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  laplacian f x












/-- The surface area $\omega_n$ of the unit sphere $S^{n-1} \subset \mathbb{R}^n$, given by
$\omega_n = 2 \pi^{n/2} / \Gamma(n/2)$ for $n \ge 1$. -/
def unitSphereArea (n : ℕ) : ℝ :=
  if n = 0 then 1 else 2 * Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)

/-- The fundamental solution $\Phi(x)$ of $-\Delta$ in $\mathbb{R}^n$ (equation 1.0.3): for
$n = 2$ it is $\tfrac{1}{2\pi}\log|x|$, and for $n \ge 3$ it is $-1/(\omega_n |x|^{n-2})$. -/
def FundSolN {n : ℕ} [Fact (2 ≤ n)] (x : Fin n → ℝ) : ℝ :=
  if n = 2 then
    (1 / (2 * Real.pi)) * Real.log (euclidNorm x)
  else
    -1 / (unitSphereArea n * (euclidNorm x) ^ (n - 2))

/-- The surface area of the unit sphere $S^2 \subset \mathbb{R}^3$ equals $4\pi$. -/
lemma unitSphereArea_three : unitSphereArea 3 = 4 * Real.pi := by
  unfold unitSphereArea
  simp only [show (3 : ℕ) ≠ 0 from by omega, ↓reduceIte]
  norm_cast
  conv_lhs =>
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 from by ring]
  rw [rpow_add Real.pi_pos, rpow_one, ← Real.sqrt_eq_rpow]
  rw [show (1 : ℝ) + 1 / 2 = 1 / 2 + 1 from by ring]
  rw [Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0)]
  rw [Real.Gamma_one_half_eq]
  have hsqrt_ne : √Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp
  ring

/-- In dimension three, the general fundamental solution `FundSolN` agrees with the
3D-specific `Phi3 = -1/(4\pi |x|)$. -/
theorem FundSolN_eq_Phi3 : ∀ [inst : Fact (2 ≤ 3)] (x : Fin 3 → ℝ),
    @FundSolN 3 inst x = Phi3 x := by
  intro inst x
  simp only [FundSolN, show (3 : ℕ) ≠ 2 from by omega, ↓reduceIte,
    show (3 : ℕ) - 2 = 1 from by omega, pow_one]
  rw [unitSphereArea_three]
  simp only [Phi3]















/-- For $n \ge 3$, on the sphere $|σ - x| = \varepsilon$ the fundamental solution satisfies
$\|\Phi(x - \sigma)\| \le C_F / \varepsilon^{n-2}$ for some constant $C_F \ge 0$. -/
theorem FundSolN_norm_on_sphere {n : ℕ} [Fact (2 ≤ n)] (hn3 : 3 ≤ n) :
    ∃ C_F : ℝ, 0 ≤ C_F ∧ ∀ (x : Fin n → ℝ) (ε : ℝ), 0 < ε →
      ∀ σ ∈ Metric.sphere x ε, ‖FundSolN (x - σ)‖ ≤ C_F / ε ^ (n - 2) := by
  have hn2 : n ≠ 2 := by omega

  have hω_pos : 0 < unitSphereArea n := by
    unfold unitSphereArea
    rw [if_neg (by omega : n ≠ 0)]
    apply div_pos
    · exact mul_pos (by norm_num : (0:ℝ) < 2) (Real.rpow_pos_of_pos Real.pi_pos _)
    · exact Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (n : ℝ) / 2)

  refine ⟨1 / unitSphereArea n, by positivity, ?_⟩
  intro x ε hε σ hσ

  have hnorm_eq : ‖x - σ‖ = ε := by
    have hdist : dist σ x = ε := hσ
    rw [← hdist, dist_eq_norm, norm_sub_rev]

  have hEN_ge : ε ≤ euclidNorm (x - σ) := by
    unfold euclidNorm
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have h_norm_le : ‖x - σ‖ ≤ Real.sqrt (∑ i : Fin n, (x - σ) i ^ 2) := by
      rw [pi_norm_le_iff_of_nonempty]
      intro b
      rw [Real.norm_eq_abs]
      have h1 : (x - σ) b ^ 2 ≤ ∑ j : Fin n, (x - σ) j ^ 2 :=
        Finset.single_le_sum (f := fun j => (x - σ) j ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ b)
      calc |(x - σ) b| = Real.sqrt ((x - σ) b ^ 2) := by rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt (∑ j : Fin n, (x - σ) j ^ 2) := Real.sqrt_le_sqrt h1
    linarith
  have hEN_pos : 0 < euclidNorm (x - σ) := by linarith

  have hFSN : FundSolN (x - σ) =
      -1 / (unitSphereArea n * euclidNorm (x - σ) ^ (n - 2)) := by
    unfold FundSolN; rw [if_neg hn2]

  rw [hFSN, Real.norm_eq_abs, abs_div, abs_neg, abs_one]
  have hprod_pos : 0 < unitSphereArea n * euclidNorm (x - σ) ^ (n - 2) :=
    mul_pos hω_pos (pow_pos hEN_pos _)
  rw [abs_of_pos hprod_pos, div_div]

  exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) < 1).le
    (mul_pos hω_pos (pow_pos hε _))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hEN_ge _) hω_pos.le)























/-- Continuity at $x$ implies that the supremum of the oscillation $|u(\sigma) - u(x)|$ over
the shrinking sphere $\partial B(x,\varepsilon)$ tends to zero as $\varepsilon \downarrow 0$. -/
theorem sup_sphere_oscillation_tendsto_zero {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    Filter.Tendsto
      (fun ε => ⨆ σ ∈ Metric.sphere x ε, |u σ - u x|)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by

  have hcont : ContinuousAt u x :=
    hu.continuousOn.continuousAt (Filter.mem_of_superset (hΩ.mem_nhds hx) subset_closure)

  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ

  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hη_pos, hη_bound⟩ := hcont (δ / 2) (half_pos hδ)

  refine ⟨η, hη_pos, fun ε hε_mem hε_dist => ?_⟩
  have hε_pos : (0 : ℝ) < ε := hε_mem
  have hε_lt_η : ε < η := by
    have h1 : |ε| < η := by simpa [dist_zero_right] using hε_dist
    rwa [abs_of_pos hε_pos] at h1

  have h_bound : ⨆ σ ∈ Metric.sphere x ε, |u σ - u x| ≤ δ / 2 := by
    apply Real.iSup_le (fun σ => ?_) (le_of_lt (half_pos hδ))
    apply Real.iSup_le (fun hσ => ?_) (le_of_lt (half_pos hδ))
    have hσ_near : dist σ x < η := by
      rw [Metric.mem_sphere.mp hσ]; linarith
    have h_u_close := hη_bound hσ_near
    rw [Real.dist_eq] at h_u_close
    linarith [abs_nonneg (u σ - u x)]

  rw [dist_zero_right]
  have h_nonneg : (0 : ℝ) ≤ ⨆ σ ∈ Metric.sphere x ε, |u σ - u x| :=
    Real.iSup_nonneg fun σ => Real.iSup_nonneg fun _ => abs_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
  linarith









/-- Green function for the domain $\Omega \subset \mathbb{R}^n$ (Definition 2.0.2 together with
the decomposition in Proposition 2.0.2): a function $G(x, y)$ on $\Omega \times \Omega$ with
$\Delta_y G(x, y) = \delta(x)$ and $G(x, \sigma) = 0$ for $\sigma \in \partial \Omega$. It is
packaged as the decomposition $G(x, y) = \Phi(x - y) - \phi(x, y)$, where the corrector
$\phi(x, \cdot)$ is harmonic in $\Omega$ with boundary data $\Phi(x - \cdot)|_{\partial\Omega}$. -/
structure GreenFunctionN (n : ℕ) [Fact (2 ≤ n)] (Ω : Set (Fin n → ℝ)) where
  G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  corrector : (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  decomposition : ∀ x y, G x y = FundSolN (x - y) - corrector x y
  boundary_vanish : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, G x σ = 0
  corrector_harmonic : ∀ x ∈ Ω, ∀ y ∈ Ω, laplacian (corrector x) y = 0
  corrector_boundary : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, corrector x σ = FundSolN (x - σ)
  corrector_reg : ∀ x ∈ Ω, ContDiffOn ℝ 2 (corrector x) (closure Ω)

/-- Instance: $2 \le 3$, supplied so that `FundSolN` and related results specialise to the
three-dimensional setting. -/
instance : Fact (2 ≤ 3) := ⟨by omega⟩













/-- Volume-integral form of the decomposition $G = \Phi - \phi$: under integrability,
$\int_\Omega f(y) G(x, y)\, dy = \int_\Omega \Phi(x-y) f(y)\, dy - \int_\Omega \phi(x, y) f(y)\, dy$. -/
theorem volume_integral_G_decomp {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionN n Ω)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hPhi_int : IntegrableOn (fun y => FundSolN (x - y) * f y) Ω)
    (hcorr_int : IntegrableOn (fun y => gf.corrector x y * f y) Ω) :
    (∫ y in Ω, f y * gf.G x y) =
    (∫ y in Ω, FundSolN (x - y) * f y) - (∫ y in Ω, gf.corrector x y * f y) := by

  have h_integrand : ∀ y, f y * gf.G x y = FundSolN (x - y) * f y - gf.corrector x y * f y := by
    intro y
    rw [gf.decomposition x y]
    ring
  simp_rw [h_integrand]

  rw [MeasureTheory.integral_sub hPhi_int hcorr_int]






end CM8
