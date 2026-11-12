/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_1
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_18
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct

open MeasureTheory Matrix Real Finset ENNReal

noncomputable section

/-- Chernoff bound for a sub-Gaussian random variable: if $X$ is sub-Gaussian
with proxy variance $\sigma^2$, then
$\mathbb{P}(X > t) \le \exp(-t^2 / (2\sigma^2))$ for any $t > 0$. -/
lemma subGaussian_chernoff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σsq : ℝ} (hσ : 0 < σsq)
    (hsg : IsSubGaussian X σsq μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | X ω > t} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * σsq)))) := by

  set s := t / σsq with hs_def
  have hs_pos : 0 < s := div_pos ht hσ

  have h_sub : {ω | X ω > t} ⊆
      {ω | ENNReal.ofReal (Real.exp (s * t)) ≤
           ENNReal.ofReal (Real.exp (s * X ω))} := by
    intro ω hω; simp only [Set.mem_setOf_eq] at *
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp_of_le (by nlinarith))

  have h_meas : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (s * X ω))) μ :=
    (hsg.exp_integrable s).1.aemeasurable.ennreal_ofReal
  have hmark := mul_meas_ge_le_lintegral₀ h_meas (ENNReal.ofReal (Real.exp (s * t)))

  have h_nn : (fun _ => (0 : ℝ)) ≤ᵐ[μ] fun ω => Real.exp (s * X ω) :=
    ae_of_all μ (fun ω => (Real.exp_pos (s * X ω)).le)
  have h_lint := (ofReal_integral_eq_lintegral_ofReal (hsg.exp_integrable s) h_nn).symm

  have h_mgf := hsg.mgf_bound s

  have h_exp_pos : (0 : ℝ) < Real.exp (s * t) := Real.exp_pos _
  have h_ne_zero : ENNReal.ofReal (Real.exp (s * t)) ≠ 0 :=
    ENNReal.ofReal_pos.mpr h_exp_pos |>.ne'
  have h_ne_top : ENNReal.ofReal (Real.exp (s * t)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_bound : ENNReal.ofReal (Real.exp (s * t)) *
      μ {ω | ENNReal.ofReal (Real.exp (s * t)) ≤
           ENNReal.ofReal (Real.exp (s * X ω))} ≤
      ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2)) := by
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω)) ∂μ := hmark
      _ = ENNReal.ofReal (∫ ω, Real.exp (s * X ω) ∂μ) := h_lint
      _ ≤ ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2)) :=
          ENNReal.ofReal_le_ofReal h_mgf
  rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl h_ne_zero) (Or.inl h_ne_top)] at h_bound
  calc μ {ω | X ω > t}
      ≤ μ {ω | ENNReal.ofReal (Real.exp (s * t)) ≤
           ENNReal.ofReal (Real.exp (s * X ω))} := measure_mono h_sub
    _ ≤ ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2)) /
          ENNReal.ofReal (Real.exp (s * t)) := h_bound
    _ = ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2) / Real.exp (s * t)) :=
        (ENNReal.ofReal_div_of_pos h_exp_pos).symm
    _ = ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2 - s * t)) := by
        rw [Real.exp_sub]
    _ = ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * σsq)))) := by
        congr 1; congr 1; rw [hs_def]; field_simp; ring

/-- Arithmetic identity: $\lceil (3 / (1/4))^n \rceil = 12^n$, used to bound the
covering-net cardinality coming from Lemma 1.18 with $\varepsilon = 1/4$. -/
lemma ceil_twelve_pow (n : ℕ) : Nat.ceil ((3 / (1/4 : ℝ)) ^ n) = 12 ^ n := by
  rw [show (3 : ℝ) / (1/4) = 12 from by norm_num]
  rw [show (12 : ℝ) ^ n = ((12 ^ n : ℕ) : ℝ) from by push_cast; ring]
  exact Nat.ceil_natCast _

local notation "⟪" x ", " y "⟫ᵣ" => @inner ℝ _ _ x y

/-- Epsilon-net reduction step in Lemma 4.2: if $\langle x, Ay\rangle \le M$ for
all $x, y$ in $1/4$-nets $N_1, N_2$ of the unit balls, then the operator norm
of $A$ satisfies $\|A\|_{op} \le 2M$. -/
theorem lemma_4_2_eps_net_reduction
    {d T : ℕ}
    (A : Matrix (Fin d) (Fin T) ℝ)
    {N₁ : Finset (EuclideanSpace ℝ (Fin d))}
    {N₂ : Finset (EuclideanSpace ℝ (Fin T))}
    (hN₁_net : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      ∃ x ∈ N₁, dist u x ≤ 1/4)
    (hN₂_net : ∀ v : EuclideanSpace ℝ (Fin T), ‖v‖ = 1 →
      ∃ y ∈ N₂, dist v y ≤ 1/4)
    (hN₁_sub : ∀ x ∈ N₁, ‖x‖ ≤ 1)
    (hN₂_sub : ∀ y ∈ N₂, ‖y‖ ≤ 1)
    (hN₁_ne : N₁.Nonempty) (hN₂_ne : N₂.Nonempty)
    (M : ℝ)
    (hM : ∀ x ∈ N₁, ∀ y ∈ N₂,
      dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
        (A.mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) ≤ M) :
    matrixOpNorm A ≤ 2 * M := by
  set f : EuclideanSpace ℝ (Fin T) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    ((Matrix.toEuclideanLin (n := Fin T) (m := Fin d) (𝕜 := ℝ)).trans
      LinearMap.toContinuousLinearMap) A with hf_def
  set α := ‖f‖ with hα_def
  have hα_nonneg : 0 ≤ α := norm_nonneg f
  show α ≤ 2 * M
  suffices h_self : α ≤ M + α / 2 by linarith
  have inner_eq_dot : ∀ (x : EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin T)),
      ⟪x, f y⟫ᵣ = dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
        (A.mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) := by
    intro x y
    have h1 : ∀ i, (f y : EuclideanSpace ℝ (Fin d)) i = (A.mulVec ((WithLp.equiv 2 (Fin T → ℝ)) y)) i := by
      intro i; rfl
    simp only [PiLp.inner_apply, dotProduct]
    congr 1; ext i
    rw [h1]
    show ((A *ᵥ (WithLp.equiv 2 (Fin T → ℝ)) y) i) * (x.ofLp i) =
      (EuclideanSpace.equiv (Fin d) ℝ) x i * (A *ᵥ (EuclideanSpace.equiv (Fin T) ℝ) y) i
    exact mul_comm _ _
  have h_bilinear : ∀ (u : EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin T)),
      ‖u‖ = 1 → ‖v‖ = 1 →
      ⟪u, f v⟫ᵣ ≤ M + α / 2 := by
    intro u v hu hv
    obtain ⟨x, hx_mem, hx_dist⟩ := hN₁_net u hu
    obtain ⟨y, hy_mem, hy_dist⟩ := hN₂_net v hv
    have hx_norm : ‖x‖ ≤ 1 := hN₁_sub x hx_mem
    have hux : ‖u - x‖ ≤ 1 / 4 := by rwa [dist_eq_norm] at hx_dist
    have hvy : ‖v - y‖ ≤ 1 / 4 := by rwa [dist_eq_norm] at hy_dist
    have hfv_bound : ‖f v‖ ≤ α := by
      calc ‖f v‖ ≤ α * ‖v‖ := f.le_opNorm v
        _ = α := by rw [hv, mul_one]
    have h_err1 : |⟪u - x, f v⟫ᵣ| ≤ α / 4 := by
      calc |⟪u - x, f v⟫ᵣ|
          ≤ ‖u - x‖ * ‖f v‖ := abs_real_inner_le_norm (u - x) (f v)
        _ ≤ (1 / 4) * α := mul_le_mul hux hfv_bound (norm_nonneg _) (by linarith)
        _ = α / 4 := by ring
    have hfvy_bound : ‖f (v - y)‖ ≤ α / 4 := by
      calc ‖f (v - y)‖ ≤ α * ‖v - y‖ := f.le_opNorm (v - y)
        _ ≤ α * (1 / 4) := mul_le_mul_of_nonneg_left hvy hα_nonneg
        _ = α / 4 := by ring
    have h_err2 : |⟪x, f (v - y)⟫ᵣ| ≤ α / 4 := by
      calc |⟪x, f (v - y)⟫ᵣ|
          ≤ ‖x‖ * ‖f (v - y)‖ := abs_real_inner_le_norm x (f (v - y))
        _ ≤ 1 * (α / 4) := mul_le_mul hx_norm hfvy_bound (norm_nonneg _) (by linarith)
        _ = α / 4 := by ring
    have h_xy : ⟪x, f y⟫ᵣ ≤ M := by
      rw [inner_eq_dot]
      exact hM x hx_mem y hy_mem
    have h_decomp : ⟪u, f v⟫ᵣ =
      ⟪x, f y⟫ᵣ + ⟪x, f (v - y)⟫ᵣ + ⟪u - x, f v⟫ᵣ := by
      have hfv : f v = f y + f (v - y) := by rw [← map_add, add_sub_cancel]
      rw [hfv, inner_add_right]
      have hu_eq : u = x + (u - x) := by abel
      conv_lhs => rw [hu_eq]
      rw [inner_add_left]
      rw [inner_add_right, inner_add_left]
      ring
    rw [h_decomp]
    have h1 : ⟪x, f (v - y)⟫ᵣ ≤ α / 4 := le_of_abs_le h_err2
    have h2 : ⟪u - x, f v⟫ᵣ ≤ α / 4 := le_of_abs_le h_err1
    linarith
  have h_unit_bound : ∀ (v : EuclideanSpace ℝ (Fin T)),
      ‖v‖ = 1 → ‖f v‖ ≤ M + α / 2 := by
    intro v hv
    by_cases hfv : f v = 0
    · rw [hfv, norm_zero]
      obtain ⟨x0, hx0⟩ := hN₁_ne
      have hx0_norm := hN₁_sub x0 hx0
      by_cases hx0_zero : x0 = 0
      · obtain ⟨y0, hy0⟩ := hN₂_ne
        have := hM x0 hx0 y0 hy0
        have : dotProduct (EuclideanSpace.equiv (Fin d) ℝ x0)
          (A.mulVec (EuclideanSpace.equiv (Fin T) ℝ y0)) ≤ M := this
        rw [hx0_zero] at this
        simp only [map_zero, zero_dotProduct] at this
        linarith
      · have hx0_norm_pos : 0 < ‖x0‖ := norm_pos_iff.mpr hx0_zero
        set u0 := (‖x0‖⁻¹ : ℝ) • x0
        have hu0_norm : ‖u0‖ = 1 := by
          rw [norm_smul, norm_inv, norm_norm]
          exact inv_mul_cancel₀ (ne_of_gt hx0_norm_pos)
        have := h_bilinear u0 v hu0_norm hv
        rw [hfv, inner_zero_right] at this
        linarith
    · set w := (‖f v‖⁻¹ : ℝ) • (f v) with hw_def
      have hw_norm : ‖w‖ = 1 := by
        rw [hw_def, norm_smul, norm_inv, norm_norm]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hfv)
      have hw_inner : ⟪w, f v⟫ᵣ = ‖f v‖ := by
        rw [hw_def, inner_smul_left, RCLike.conj_to_real,
            real_inner_self_eq_norm_mul_norm]
        field_simp
      calc ‖f v‖ = ⟪w, f v⟫ᵣ := hw_inner.symm
        _ ≤ M + α / 2 := h_bilinear w v hw_norm hv
  rw [hα_def]
  apply ContinuousLinearMap.opNorm_le_bound f _ (fun v => ?_)
  · by_cases hf_zero : f = 0
    · rw [hf_zero, norm_zero]; simp only [zero_div, add_zero]
      obtain ⟨x0, hx0⟩ := hN₁_ne
      obtain ⟨y0, hy0⟩ := hN₂_ne
      have hA_zero : A = 0 := by
        have hlin : Matrix.toEuclideanLin (n := Fin T) (m := Fin d) (𝕜 := ℝ) A = 0 := by
          have hfz : ∀ v, f v = 0 := by intro v; rw [hf_zero]; simp
          ext v
          have h_eq : (f v : EuclideanSpace ℝ (Fin d)) = toEuclideanLin A v := rfl
          have := hfz v
          rw [h_eq] at this
          simp only [LinearMap.zero_apply, this]
        exact (Matrix.toEuclideanLin (n := Fin T) (m := Fin d) (𝕜 := ℝ)).injective
          (by rw [hlin, map_zero])
      have : dotProduct (EuclideanSpace.equiv (Fin d) ℝ x0)
        (A.mulVec (EuclideanSpace.equiv (Fin T) ℝ y0)) = 0 := by
        rw [hA_zero, Matrix.zero_mulVec, dotProduct_zero]
      linarith [hM x0 hx0 y0 hy0]
    · obtain ⟨v0, hv0⟩ := ContinuousLinearMap.exists_ne_zero hf_zero
      have hv0_ne : v0 ≠ 0 := by
        intro h; rw [h] at hv0; simp at hv0
      have hv0_norm_pos : 0 < ‖v0‖ := norm_pos_iff.mpr hv0_ne
      set v1 := (‖v0‖⁻¹ : ℝ) • v0
      have hv1_norm : ‖v1‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm]
        exact inv_mul_cancel₀ (ne_of_gt hv0_norm_pos)
      have := h_unit_bound v1 hv1_norm
      linarith [norm_nonneg (f v1)]
  · by_cases hv : v = 0
    · simp [hv]
    · have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      set v1 := (‖v‖⁻¹ : ℝ) • v with hv1_def
      have hv1_norm : ‖v1‖ = 1 := by
        rw [hv1_def, norm_smul, norm_inv, norm_norm]
        exact inv_mul_cancel₀ (ne_of_gt hv_norm_pos)
      have hfv1 : ‖f v1‖ ≤ M + α / 2 := h_unit_bound v1 hv1_norm
      calc ‖f v‖ = ‖f (‖v‖ • v1)‖ := by
            rw [hv1_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hv_norm_pos), one_smul]
        _ = ‖‖v‖ • f v1‖ := by rw [map_smul]
        _ = ‖v‖ * ‖f v1‖ := by rw [norm_smul, Real.norm_of_nonneg (le_of_lt hv_norm_pos)]
        _ ≤ ‖v‖ * (M + α / 2) := mul_le_mul_of_nonneg_left hfv1 (le_of_lt hv_norm_pos)
        _ = (M + α / 2) * ‖v‖ := by ring

/-- **Lemma 4.2 (tail bound).** For a sub-Gaussian matrix $A$ with proxy variance
$\sigma^2$,
$\mathbb{P}(\|A\|_{op} > t) \le 12^{d+T} \exp(-t^2/(8\sigma^2))$
for any $t > 0$. -/
theorem lemma_4_2_operator_norm_tail
    {d T : ℕ} (hd : 0 < d) (hT : 0 < T)
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} (hμ : IsProbabilityMeasure μ)
    {A : Ω → Matrix (Fin d) (Fin T) ℝ} {σsq : ℝ} (hσ : 0 < σsq)
    (hsg : @IsSubGaussianMatrix Ω _ d T A σsq μ hμ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | matrixOpNorm (A ω) > t} ≤
      ENNReal.ofReal ((12 : ℝ) ^ (d + T) * Real.exp (-(t ^ 2 / (8 * σsq)))) := by

  have heps : (0 : ℝ) < 1 / 4 := by norm_num
  have heps_lt : (1 : ℝ) / 4 < 1 := by norm_num
  obtain ⟨N₁, hN₁_net, hN₁_card⟩ :=
    lemma_1_18_covering_number_euclidean_ball hd (1/4) heps heps_lt
  obtain ⟨N₂, hN₂_net, hN₂_card⟩ :=
    lemma_1_18_covering_number_euclidean_ball hT (1/4) heps heps_lt

  have hN₁_card' : N₁.card ≤ 12 ^ d := by rw [← ceil_twelve_pow]; exact hN₁_card
  have hN₂_card' : N₂.card ≤ 12 ^ T := by rw [← ceil_twelve_pow]; exact hN₂_card

  have hN₁_sub : ∀ x ∈ N₁, ‖x‖ ≤ 1 := by
    intro x hx; have := hN₁_net.1 hx
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hN₂_sub : ∀ y ∈ N₂, ‖y‖ ≤ 1 := by
    intro y hy; have := hN₂_net.1 hy
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hN₁_cov : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      ∃ x ∈ N₁, dist u x ≤ 1 / 4 := by
    intro u hu
    obtain ⟨x, hx_mem, hx_dist⟩ := hN₁_net.2 u (by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith [hu])
    exact ⟨x, hx_mem, by rwa [dist_comm]⟩
  have hN₂_cov : ∀ v : EuclideanSpace ℝ (Fin T), ‖v‖ = 1 →
      ∃ y ∈ N₂, dist v y ≤ 1 / 4 := by
    intro v hv
    obtain ⟨y, hy_mem, hy_dist⟩ := hN₂_net.2 v (by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith [hv])
    exact ⟨y, hy_mem, by rwa [dist_comm]⟩

  have hN₁_ne : N₁.Nonempty := by
    obtain ⟨x, hx, _⟩ := hN₁_cov (EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1) (by
      rw [EuclideanSpace.norm_single]; simp)
    exact ⟨x, hx⟩
  have hN₂_ne : N₂.Nonempty := by
    obtain ⟨y, hy, _⟩ := hN₂_cov (EuclideanSpace.single (⟨0, hT⟩ : Fin T) 1) (by
      rw [EuclideanSpace.norm_single]; simp)
    exact ⟨y, hy⟩


  have h_contain : {ω | matrixOpNorm (A ω) > t} ⊆
      ⋃ x ∈ N₁, ⋃ y ∈ N₂, {ω | dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
        ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) > t / 2} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra h_not
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at h_not
    have h_all_le : ∀ x ∈ N₁, ∀ y ∈ N₂,
        dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
          ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) ≤ t / 2 := by
      intro x hx y hy; exact le_of_not_gt (h_not x hx y hy)
    have h_bound := lemma_4_2_eps_net_reduction (A ω) hN₁_cov hN₂_cov
      hN₁_sub hN₂_sub hN₁_ne hN₂_ne (t / 2) h_all_le
    linarith


  have h_each : ∀ x ∈ N₁, ∀ y ∈ N₂,
      μ {ω | dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
        ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) > t / 2} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 / (8 * σsq)))) := by
    intro x hx y hy

    by_cases hx0 : x = 0
    · have h_empty : {ω | dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
          ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) > t / 2} = ∅ := by
        ext ω; simp [hx0, show ¬ (0 : ℝ) > t / 2 from by linarith]
      rw [h_empty, measure_empty]; exact zero_le _
    by_cases hy0 : y = 0
    · have : ∀ ω, dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
          ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) = 0 := by
        intro ω; rw [hy0]; simp [dotProduct, mulVec, EuclideanSpace.equiv]
      have h_empty : {ω | dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
          ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) > t / 2} = ∅ := by
        ext ω; simp [this ω, show ¬ (0 : ℝ) > t / 2 from by linarith]
      rw [h_empty, measure_empty]; exact zero_le _

    have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    set xHat := (‖x‖⁻¹ : ℝ) • x
    set yHat := (‖y‖⁻¹ : ℝ) • y
    have hxn : ‖xHat‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ (ne_of_gt hx_pos)
    have hyn : ‖yHat‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ (ne_of_gt hy_pos)

    have hsg_unit := hsg xHat yHat hxn hyn
    have h_chern := subGaussian_chernoff hσ hsg_unit (t / 2) (by linarith)

    have h_prod_le : ‖x‖ * ‖y‖ ≤ 1 := by
      have := mul_le_mul (hN₁_sub x hx) (hN₂_sub y hy) (norm_nonneg _) zero_le_one
      simpa using this
    have h_sub_event : {ω | dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
        ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) > t / 2} ⊆
        {ω | dotProduct (EuclideanSpace.equiv (Fin d) ℝ xHat)
        ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ yHat)) > t / 2} := by
      intro ω hω; simp only [Set.mem_setOf_eq] at *


      have h_scale : dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
          ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) =
          ‖x‖ * ‖y‖ * dotProduct (EuclideanSpace.equiv (Fin d) ℝ xHat)
          ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ yHat)) := by
        show dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
            ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) =
            ‖x‖ * ‖y‖ * dotProduct (EuclideanSpace.equiv (Fin d) ℝ ((‖x‖⁻¹ : ℝ) • x))
            ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ ((‖y‖⁻¹ : ℝ) • y)))
        rw [map_smul, map_smul, mulVec_smul, smul_dotProduct, dotProduct_smul,
            smul_eq_mul, smul_eq_mul]
        field_simp
      rw [h_scale] at hω
      have h_pos_dp : 0 < dotProduct (EuclideanSpace.equiv (Fin d) ℝ xHat)
          ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ yHat)) := by
        by_contra h_neg; push_neg at h_neg
        have : ‖x‖ * ‖y‖ * dotProduct (EuclideanSpace.equiv (Fin d) ℝ xHat)
          ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ yHat)) ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h_neg
        linarith
      have h_ineq : ‖x‖ * ‖y‖ * dotProduct (EuclideanSpace.equiv (Fin d) ℝ xHat)
            ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ yHat)) ≤
          dotProduct (EuclideanSpace.equiv (Fin d) ℝ xHat)
            ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ yHat)) := by
        nlinarith [h_prod_le, h_pos_dp]
      linarith [h_ineq, hω]

    calc μ {ω | dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
          ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) > t / 2}
        ≤ μ {ω | dotProduct (EuclideanSpace.equiv (Fin d) ℝ xHat)
          ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ yHat)) > t / 2} :=
            measure_mono h_sub_event
      _ ≤ ENNReal.ofReal (Real.exp (-((t / 2) ^ 2 / (2 * σsq)))) := h_chern
      _ = ENNReal.ofReal (Real.exp (-(t ^ 2 / (8 * σsq)))) := by
          congr 1; congr 1; ring

  calc μ {ω | matrixOpNorm (A ω) > t}
      ≤ μ (⋃ x ∈ N₁, ⋃ y ∈ N₂, {ω | dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
          ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) > t / 2}) :=
          measure_mono h_contain
    _ ≤ ∑ x ∈ N₁, μ (⋃ y ∈ N₂, {ω | dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
          ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) > t / 2}) := by
        exact measure_biUnion_finset_le N₁ _
    _ ≤ ∑ x ∈ N₁, ∑ y ∈ N₂,
          ENNReal.ofReal (Real.exp (-(t ^ 2 / (8 * σsq)))) := by
        apply Finset.sum_le_sum; intro x hx
        calc μ (⋃ y ∈ N₂, {ω | dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
              ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) > t / 2})
            ≤ ∑ y ∈ N₂, μ {ω | dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
              ((A ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ y)) > t / 2} :=
                measure_biUnion_finset_le N₂ _
          _ ≤ ∑ y ∈ N₂, ENNReal.ofReal (Real.exp (-(t ^ 2 / (8 * σsq)))) :=
              Finset.sum_le_sum (fun y hy => h_each x hx y hy)
    _ = ↑(N₁.card * N₂.card) * ENNReal.ofReal (Real.exp (-(t ^ 2 / (8 * σsq)))) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
            ← mul_assoc, ← Nat.cast_mul]
    _ ≤ ↑(12 ^ (d + T)) * ENNReal.ofReal (Real.exp (-(t ^ 2 / (8 * σsq)))) := by
        apply mul_le_mul_right'
        have h_card : N₁.card * N₂.card ≤ 12 ^ (d + T) := by
          calc N₁.card * N₂.card
              ≤ 12 ^ d * 12 ^ T := Nat.mul_le_mul hN₁_card' hN₂_card'
            _ = 12 ^ (d + T) := (pow_add 12 d T).symm
        exact_mod_cast h_card
    _ = ENNReal.ofReal ((12 : ℝ) ^ (d + T) * Real.exp (-(t ^ 2 / (8 * σsq)))) := by
        rw [show (12 : ℝ≥0∞) = ENNReal.ofReal 12 from by
              rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) from by norm_num,
                  ENNReal.ofReal_natCast]; norm_num,
            ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 12),
            ← ENNReal.ofReal_mul (by positivity)]

/-- **Lemma 4.2 (high-probability bound).** With probability at least $1 - \delta$,
the operator norm of a sub-Gaussian matrix $A$ with proxy variance $\sigma^2$
satisfies
$\|A\|_{op} \le 4\sigma \sqrt{\log(12)\cdot \max(d, T)} + 2\sigma \sqrt{2 \log(1/\delta)}$. -/
theorem lemma_4_2_operator_norm_high_prob
    {d T : ℕ} (hd : 0 < d) (hT : 0 < T)
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} (hμ : IsProbabilityMeasure μ)
    {A : Ω → Matrix (Fin d) (Fin T) ℝ} {σsq : ℝ} (hσ : 0 < σsq)
    (hsg : @IsSubGaussianMatrix Ω _ d T A σsq μ hμ)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    μ {ω | matrixOpNorm (A ω) >
      4 * Real.sqrt σsq * Real.sqrt (Real.log 12 * ↑(d ⊔ T)) +
      2 * Real.sqrt σsq * Real.sqrt (2 * Real.log (1 / δ))} ≤
      ENNReal.ofReal δ := by

  set t₀ := 4 * Real.sqrt σsq * Real.sqrt (Real.log 12 * ↑(d ⊔ T)) +
    2 * Real.sqrt σsq * Real.sqrt (2 * Real.log (1 / δ)) with ht₀_def

  have hlog12 : 0 < Real.log 12 := Real.log_pos (by norm_num : (1 : ℝ) < 12)
  have hdT_pos : (0 : ℝ) < ↑(d ⊔ T) := by
    exact_mod_cast (show 0 < d ⊔ T from lt_of_lt_of_le hd le_sup_left)
  have hlog_inv : 0 < Real.log (1 / δ) := Real.log_pos (by
    rw [one_div]; exact (one_lt_inv₀ hδ_pos).mpr hδ_lt)
  have hsqrt_σ : 0 < Real.sqrt σsq := Real.sqrt_pos_of_pos hσ
  have ht₀_pos : 0 < t₀ := by positivity

  have h_tail := lemma_4_2_operator_norm_tail hd hT hμ hσ hsg t₀ ht₀_pos

  calc μ {ω | matrixOpNorm (A ω) > t₀}
      ≤ ENNReal.ofReal ((12 : ℝ) ^ (d + T) * Real.exp (-(t₀ ^ 2 / (8 * σsq)))) := h_tail
    _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal


        set a := 4 * Real.sqrt σsq * Real.sqrt (Real.log 12 * ↑(d ⊔ T))
        set b := 2 * Real.sqrt σsq * Real.sqrt (2 * Real.log (1 / δ))
        have ha_pos : 0 < a := by positivity
        have hb_pos : 0 < b := by positivity

        have ha_sq : a ^ 2 = 16 * σsq * (Real.log 12 * ↑(d ⊔ T)) := by
          rw [show a = 4 * Real.sqrt σsq * Real.sqrt (Real.log 12 * ↑(d ⊔ T)) from rfl]
          rw [mul_pow, mul_pow, sq_sqrt hσ.le,
              sq_sqrt (mul_nonneg hlog12.le hdT_pos.le)]
          ring

        have hb_sq : b ^ 2 = 8 * σsq * Real.log (1 / δ) := by
          rw [show b = 2 * Real.sqrt σsq * Real.sqrt (2 * Real.log (1 / δ)) from rfl]
          rw [mul_pow, mul_pow, sq_sqrt hσ.le,
              sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hlog_inv.le)]
          ring

        have ht₀_sq_ge : t₀ ^ 2 ≥ a ^ 2 + b ^ 2 := by
          have : t₀ = a + b := rfl
          rw [this]; nlinarith [mul_pos ha_pos hb_pos]

        have h_dT_le : d + T ≤ 2 * (d ⊔ T) := by omega

        have h_a_absorbs : a ^ 2 / (8 * σsq) ≥ ↑(d + T) * Real.log 12 := by
          rw [ha_sq, show 16 * σsq * (Real.log 12 * ↑(d ⊔ T)) / (8 * σsq) =
            2 * Real.log 12 * ↑(d ⊔ T) from by field_simp; ring]
          have : (↑(d + T) : ℝ) ≤ 2 * ↑(d ⊔ T) := by exact_mod_cast h_dT_le
          nlinarith [hlog12]

        have h_b_absorbs : b ^ 2 / (8 * σsq) = Real.log (1 / δ) := by
          rw [hb_sq]; field_simp


        have h_exp_bound : t₀ ^ 2 / (8 * σsq) ≥
            ↑(d + T) * Real.log 12 + Real.log (1 / δ) := by
          have h8σ_pos : 0 < 8 * σsq := by positivity
          calc t₀ ^ 2 / (8 * σsq)
              ≥ (a ^ 2 + b ^ 2) / (8 * σsq) := by
                exact div_le_div_of_nonneg_right ht₀_sq_ge (by positivity)
            _ = a ^ 2 / (8 * σsq) + b ^ 2 / (8 * σsq) := by
                rw [add_div]
            _ ≥ ↑(d + T) * Real.log 12 + Real.log (1 / δ) := by
                linarith [h_a_absorbs, h_b_absorbs]


        have h12_pos : (0 : ℝ) < 12 ^ (d + T) := by positivity

        have h_key : (12 : ℝ) ^ (d + T) *
            Real.exp (-(↑(d + T) * Real.log 12 + Real.log (1 / δ))) = δ := by
          have hlog_cast : (↑(d + T) : ℝ) * Real.log 12 = Real.log ((12 : ℝ) ^ (d + T)) := by
            rw [Real.log_pow]

          rw [hlog_cast, show -(Real.log ((12 : ℝ) ^ (d + T)) + Real.log (1 / δ)) =
              -Real.log ((12 : ℝ) ^ (d + T)) + -Real.log (1 / δ) from by ring,
              Real.exp_add, ← Real.log_inv, ← Real.log_inv,
              Real.exp_log (by positivity : (0 : ℝ) < ((12 : ℝ) ^ (d + T))⁻¹),
              Real.exp_log (by positivity : (0 : ℝ) < (1 / δ)⁻¹)]
          field_simp
        calc (12 : ℝ) ^ (d + T) * Real.exp (-(t₀ ^ 2 / (8 * σsq)))
            ≤ 12 ^ (d + T) * Real.exp (-(↑(d + T) * Real.log 12 + Real.log (1 / δ))) := by
              apply mul_le_mul_of_nonneg_left _ h12_pos.le
              exact Real.exp_le_exp_of_le (by linarith [h_exp_bound])
          _ = δ := h_key

end
