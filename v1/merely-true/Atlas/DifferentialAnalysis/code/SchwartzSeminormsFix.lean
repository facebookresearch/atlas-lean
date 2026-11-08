/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

open scoped SchwartzMap

noncomputable section

namespace SchwartzSeminorms

variable
  {𝕜 : Type*} [NormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- Pointwise weighted derivative bound by Schwartz seminorms: for `k, n ≤ K`,
`(1 + ‖x‖)^k · ‖∂^n f(x)‖ ≤ 2^K · sup_{m ≤ (K, K)} (Schwartz seminorm m of f)`. -/
theorem weighted_norm_le_sup_seminorm {K : ℕ} {k n : ℕ} (hk : k ≤ K) (hn : n ≤ K)
    (f : 𝓢(E, F)) (x : E) :
    (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤
      2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f :=
  SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (K, K)) hk hn f x

/-- Trivial comparison: `‖x‖^k ≤ (1 + ‖x‖)^k` pointwise, with the derivative factor common. -/
theorem monomial_norm_le_weighted_norm (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤
      (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ := by
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg x) (le_add_of_nonneg_left zero_le_one) k

/-- Uniform comparison of individual Schwartz seminorms with the supremum: for `k, n ≤ K`,
`‖f‖_{k,n} ≤ 2^K · sup_{(k',n') ≤ (K, K)} ‖f‖_{k',n'}`. -/
theorem seminorm_le_two_pow_mul_sup_seminorm (K : ℕ) {k n : ℕ} (hk : k ≤ K) (hn : n ≤ K)
    (f : 𝓢(E, F)) :
    SchwartzMap.seminorm 𝕜 k n f ≤
      2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
  apply SchwartzMap.seminorm_le_bound 𝕜 k n f
  · positivity
  · intro x
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖
        ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ :=
          monomial_norm_le_weighted_norm k n f x
      _ ≤ 2 ^ K * ((Finset.Iic (K, K)).sup
          (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2)) f :=
        weighted_norm_le_sup_seminorm hk hn f x

/-- Each Schwartz seminorm `‖f‖_{k,n}` with `k, n ≤ K` is bounded by the supremum over the
finite set `Iic (K, K)` of such seminorms. -/
theorem individual_le_sup_seminorm {K : ℕ} {k n : ℕ} (hk : k ≤ K) (hn : n ≤ K)
    (f : 𝓢(E, F)) :
    SchwartzMap.seminorm 𝕜 k n f ≤
      (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
  apply Seminorm.le_def.1
  exact Finset.le_sup_of_le (Finset.mem_Iic.2 <|
    Prod.mk_le_mk.2 ⟨hk, hn⟩) le_rfl

/-- Pointwise monotonicity of weighted derivative bounds: for `p ≤ K`,
`‖x‖^p · ‖∂^q f(x)‖ ≤ (1 + ‖x‖)^K · ‖∂^q f(x)‖`. -/
theorem monomial_le_one_add_pow_pointwise {K : ℕ} {p q : ℕ} (hp : p ≤ K)
    (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ p * ‖iteratedFDeriv ℝ q (⇑f) x‖ ≤
      (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ q (⇑f) x‖ := by
  gcongr
  calc ‖x‖ ^ p ≤ (1 + ‖x‖) ^ p :=
        pow_le_pow_left₀ (norm_nonneg x) (le_add_of_nonneg_left zero_le_one) p
    _ ≤ (1 + ‖x‖) ^ K :=
        pow_le_pow_right₀ (by linarith [norm_nonneg x]) hp

/-- Reformulation of the seminorm-supremum bound using the `(1 + ‖x‖)^K` weight: for
`p, q ≤ K`, `‖f‖_{p,q} ≤ 2^K · sup_{(k, n) ≤ (K, K)} ‖f‖_{k,n}`. -/
theorem seminorm_le_weighted_via_one_add {K : ℕ} {p q : ℕ} (hp : p ≤ K) (hq : q ≤ K)
    (f : 𝓢(E, F)) :
    SchwartzMap.seminorm 𝕜 p q f ≤
      2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
  apply SchwartzMap.seminorm_le_bound 𝕜 p q f (by positivity)
  intro x
  calc ‖x‖ ^ p * ‖iteratedFDeriv ℝ q (⇑f) x‖
      ≤ (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ q (⇑f) x‖ :=
        monomial_le_one_add_pow_pointwise hp f x
    _ ≤ 2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f :=
        SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (K, K)) le_rfl hq f x

end SchwartzSeminorms

end
