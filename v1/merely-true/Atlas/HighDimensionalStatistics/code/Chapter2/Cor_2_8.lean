/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_6

open Matrix Finset BigOperators MeasureTheory Real

/-- **Corollary 2.8**: High-probability MSE bound for sparse least-squares estimators
under sub-Gaussian noise; with probability at least `1 - δ`, the in-sample MSE is
controlled by a sparsity-times-log-dimension term. -/
theorem cor_2_8_mse_prob
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} (hn : 0 < n)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ)
    (ε : Ω → Fin n → ℝ)
    (θhat : Ω → Fin d → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hkd : 2 * k ≤ d)
    (σ : ℝ) (hσ : 0 < σ)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)

    (hhat_sparse : ∀ ω, (univ.filter (fun j => θhat ω j ≠ 0)).card ≤ k)

    (hstar_sparse : (univ.filter (fun j => θstar j ≠ 0)).card ≤ k)

    (hLS : ∀ ω, ∀ θ : Fin d → ℝ,
      (univ.filter (fun j => θ j ≠ 0)).card ≤ k →
      dotProduct ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω))
                 ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω)) ≤
      dotProduct ((X.mulVec θstar + ε ω) - X.mulVec θ)
                 ((X.mulVec θstar + ε ω) - X.mulVec θ))

    (hsubG : ∀ (v : Fin n → ℝ),
      dotProduct v v ≤ 1 →
      ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ ∧
        ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤
        Real.exp (s ^ 2 * σ ^ 2 / 2)) :
    μ {ω | (1 / (n : ℝ)) *
      dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) ≤
      32 * σ ^ 2 / ↑n * (2 * ↑k * Real.log (Real.exp 1 * ↑d / (2 * ↑k))
        + 2 * ↑k * Real.log 6 + Real.log (1 / δ))} ≥
    ENNReal.ofReal (1 - δ) :=
  thm_2_6_sparse_ls_high_prob hn X θstar ε θhat k hk hkd σ hσ δ hδ_pos hδ_le
    hhat_sparse hstar_sparse hLS hsubG
