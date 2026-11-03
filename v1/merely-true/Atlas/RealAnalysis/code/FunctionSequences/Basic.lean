/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Filter Topology

/-- `ConvergesPointwise f g S` states that the sequence of functions `f n` converges pointwise
to `g` on `S`: for every `x ∈ S`, the sequence `f n x` tends to `g x` as `n → ∞`. -/
def ConvergesPointwise (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ x ∈ S, Tendsto (fun n => f n x) atTop (nhds (g x))

/-- Uniform convergence of `f n` to `g` on `S` is equivalent to the classical `ε`-`M`
formulation: for every `ε > 0`, there exists `M ∈ ℕ` such that for all `n ≥ M` and all
`x ∈ S`, `|f n x - g x| < ε`. -/
theorem uniform_convergence_iff (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (S : Set ℝ) :
    TendstoUniformlyOn f g atTop S ↔
    ∀ ε > 0, ∃ M : ℕ, ∀ n ≥ M, ∀ x ∈ S, |f n x - g x| < ε := by
  rw [Metric.tendstoUniformlyOn_iff]
  constructor
  · intro h ε hε
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (h ε hε)
    exact ⟨M, fun n hn x hx => by rw [← Real.dist_eq, dist_comm]; exact hM n hn x hx⟩
  · intro h ε hε
    obtain ⟨M, hM⟩ := h ε hε
    rw [Filter.eventually_atTop]
    exact ⟨M, fun n hn x hx => by rw [Real.dist_eq, ← abs_sub_comm]; exact hM n hn x hx⟩

/-- Weierstrass M-test: if `|f j x| ≤ M j` for all `j` and all `x ∈ S`, and `∑ M j` converges,
then for every `x ∈ S` the series `∑ f j x` converges (absolutely), and the partial sums
`∑_{j < n} f j x` converge uniformly on `S` to `∑' j, f j x`. -/
theorem weierstrass_m_test (f : ℕ → ℝ → ℝ) (M : ℕ → ℝ) (S : Set ℝ)
    (hM : ∀ j, ∀ x ∈ S, |f j x| ≤ M j) (hMsum : Summable M) :
    (∀ x ∈ S, Summable (fun j => f j x)) ∧
    TendstoUniformlyOn (fun n x => ∑ j ∈ Finset.range n, f j x)
      (fun x => ∑' j, f j x) Filter.atTop S := by
  have hfu : ∀ n, ∀ x ∈ S, ‖f n x‖ ≤ M n := by
    intro n x hx
    rw [Real.norm_eq_abs]
    exact hM n x hx
  exact ⟨fun x hx => Summable.of_norm_bounded (g := M) hMsum (fun i => hfu i x hx),
         tendstoUniformlyOn_tsum_nat hMsum hfu⟩
