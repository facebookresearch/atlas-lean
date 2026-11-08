/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.DifferentialOperators
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Normed.Module.RCLike.Real

open scoped SchwartzMap
open TemperedDistribution MvPolynomial Metric

noncomputable section

namespace DifferentialOperators

variable {n : ℕ}

/-- The principal symbol of `P` (a polynomial in the cotangent variables of order `m`)
evaluated at a real covector `ξ ∈ ℝⁿ`, viewed as a complex number by inclusion `ℝ ↪ ℂ`. -/
def evalPrincipalSymbolReal (m : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    (Fin n → ℝ) → ℂ :=
  fun ξ => MvPolynomial.eval (fun i => (ξ i : ℂ)) (principalSymbol n m P)

/-- The real-evaluation of the principal symbol `ξ ↦ σ_m(P)(ξ)` is continuous in `ξ ∈ ℝⁿ`,
since it is a polynomial composed with the coordinate-wise inclusion `ℝ ↪ ℂ`. -/
theorem continuous_evalPrincipalSymbolReal (m : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    Continuous (evalPrincipalSymbolReal m P) := by
  show Continuous (fun ξ : Fin n → ℝ =>
    MvPolynomial.eval (fun i => (ξ i : ℂ)) (principalSymbol n m P))
  exact (MvPolynomial.continuous_eval (principalSymbol n m P)).comp
    (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))

/-- Homogeneity of the principal symbol: scaling the variable by `t` multiplies the value of the
principal symbol of degree `m` by `t^m`. Used to reduce the elliptic lower bound on `ℝⁿ` to a
lower bound on the unit sphere. -/
theorem eval_homogeneous_smul (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (t : ℂ) (ξ : Fin n → ℂ) :
    MvPolynomial.eval (fun i => t * ξ i) (principalSymbol n m P) =
      t ^ m * MvPolynomial.eval ξ (principalSymbol n m P) := by
  simp only [principalSymbol_def]
  set Q := homogeneousComponent m P with hQ_def
  have hQ_hom : Q.IsHomogeneous m := homogeneousComponent_isHomogeneous m P
  rw [eval_eq, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hQ_hom.degree_eq_sum_deg_support hd]
  ring

/-- The unit sphere of `Fin n → ℝ` is nonempty whenever `n > 0`, since this guarantees the
underlying space has nontrivial points of unit norm. -/
lemma sphere_nonempty_of_pos (hn : 0 < n) :
    (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact NormedSpace.sphere_nonempty.mpr (le_of_lt one_pos)

/-- Sphere version of the elliptic lower bound: for any elliptic polynomial `P` of order `m`,
the principal symbol is bounded below in modulus by a positive constant on the unit sphere.
Proved by extracting a minimizer of the continuous function `‖σ_m(P)(ξ)‖` on the compact
sphere and noting that the minimum is nonzero by ellipticity. -/
theorem elliptic_lower_bound_sphere (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : Fin n → ℝ, ‖ξ‖ = 1 →
      c ≤ ‖evalPrincipalSymbolReal m P ξ‖ := by
  have hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere 0 1
  have hne := sphere_nonempty_of_pos hn
  have hcont : ContinuousOn (fun ξ : Fin n → ℝ => ‖evalPrincipalSymbolReal m P ξ‖)
      (Metric.sphere (0 : Fin n → ℝ) 1) :=
    (continuous_norm.comp (continuous_evalPrincipalSymbolReal m P)).continuousOn
  obtain ⟨ξ₀, hξ₀_mem, hξ₀_min⟩ := hS.exists_isMinOn hne hcont
  have hξ₀_norm : ‖ξ₀‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hξ₀_mem
  have hξ₀_ne : ξ₀ ≠ 0 := by intro h; rw [h] at hξ₀_norm; simp at hξ₀_norm
  have heval_ne : evalPrincipalSymbolReal m P ξ₀ ≠ 0 := hP ξ₀ hξ₀_ne
  exact ⟨‖evalPrincipalSymbolReal m P ξ₀‖, norm_pos_iff.mpr heval_ne, fun ξ hξ =>
    hξ₀_min (by rwa [Metric.mem_sphere, dist_zero_right])⟩

/-- Elliptic lower bound on all of `ℝⁿ`: for an elliptic operator of order `m`, there exists a
positive constant `c` such that `c · ‖ξ‖^m ≤ ‖σ_m(P)(ξ)‖` for every `ξ ∈ ℝⁿ`. Proved by
combining the sphere lower bound with the homogeneity `σ_m(P)(tξ) = t^m σ_m(P)(ξ)`. -/
theorem elliptic_lower_bound (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : Fin n → ℝ,
      c * ‖ξ‖ ^ m ≤ ‖evalPrincipalSymbolReal m P ξ‖ := by
  obtain ⟨c, hc_pos, hc_bound⟩ := elliptic_lower_bound_sphere m P hP hn
  refine ⟨c, hc_pos, fun ξ => ?_⟩
  by_cases hξ : ξ = 0
  · subst hξ
    by_cases hm : m = 0
    ·
      subst hm
      simp only [pow_zero, mul_one]
      obtain ⟨ξ₁, hξ₁⟩ := sphere_nonempty_of_pos hn
      rw [Metric.mem_sphere, dist_zero_right] at hξ₁
      have h0 : evalPrincipalSymbolReal 0 P 0 = evalPrincipalSymbolReal 0 P ξ₁ := by
        unfold evalPrincipalSymbolReal
        have heq : (fun i : Fin n => ((0 : Fin n → ℝ) i : ℂ)) =
            (fun i => (0 : ℂ) * (ξ₁ i : ℂ)) := by ext i; simp
        rw [heq, eval_homogeneous_smul 0 P 0 (fun i => (ξ₁ i : ℂ))]
        simp
      rw [h0]; exact hc_bound ξ₁ hξ₁
    ·
      rw [norm_zero, zero_pow hm, mul_zero]; exact norm_nonneg _
  ·
    have hξ_norm_pos : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hξ_norm_ne : ‖ξ‖ ≠ 0 := ne_of_gt hξ_norm_pos
    set ξhat : Fin n → ℝ := fun i => ξ i / ‖ξ‖ with ξhat_def
    have hξhat_norm : ‖ξhat‖ = 1 := by
      have : ξhat = ‖ξ‖⁻¹ • ξ := by
        ext i; simp [ξhat_def, div_eq_mul_inv, mul_comm]
      rw [this, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hξ_norm_ne]
    have h_sphere := hc_bound ξhat hξhat_norm

    have h_homog : evalPrincipalSymbolReal m P ξ =
        (↑‖ξ‖ : ℂ) ^ m * evalPrincipalSymbolReal m P ξhat := by
      unfold evalPrincipalSymbolReal
      have htx : (fun i => (ξ i : ℂ)) = (fun i => ↑‖ξ‖ * (ξhat i : ℂ)) := by
        ext i
        simp only [ξhat_def]
        push_cast
        rw [mul_div_cancel₀ _ (by exact_mod_cast hξ_norm_ne)]
      rw [htx, eval_homogeneous_smul]
    rw [h_homog, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg ξ), mul_comm]
    exact mul_le_mul_of_nonneg_left h_sphere (pow_nonneg (norm_nonneg _) _)

end DifferentialOperators

end
