/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod

noncomputable section

namespace Burger

/-- A function $u(t, x)$ is a (classical) solution of Burger's equation
$\partial_t u + u\,\partial_x u = 0$ if it is $C^1$ and satisfies the PDE pointwise. -/
def IsBurgerSolution (u : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 (Function.uncurry u) ∧
    ∀ t x, deriv (fun t' => u t' x) t + u t x * deriv (fun x' => u t x') x = 0

/-- A pair $(\gamma_0, \gamma_1)$ is a characteristic curve of Burger's equation if
$\frac{d}{ds}\gamma_0 = 1$ and $\frac{d}{ds}\gamma_1 = u(\gamma_0(s), \gamma_1(s))$
(Definition 2.0.1). -/
def IsCharacteristicCurve (u : ℝ → ℝ → ℝ) (γ₀ γ₁ : ℝ → ℝ) : Prop :=
  (∀ s, deriv γ₀ s = 1) ∧ (∀ s, deriv γ₁ s = u (γ₀ s) (γ₁ s))

/-- Helper: if $u$ is $C^1$ and $\gamma_0, \gamma_1$ are differentiable, then
$s \mapsto u(\gamma_0(s), \gamma_1(s))$ is differentiable. -/
lemma differentiable_along_char (u : ℝ → ℝ → ℝ) (γ₀ γ₁ : ℝ → ℝ)
    (hC1 : ContDiff ℝ 1 (Function.uncurry u))
    (hγ₀_diff : Differentiable ℝ γ₀)
    (hγ₁_diff : Differentiable ℝ γ₁) :
    Differentiable ℝ (fun s => u (γ₀ s) (γ₁ s)) :=
  hC1.differentiable_one.comp (hγ₀_diff.prodMk hγ₁_diff)

/-- If $u$ is a $C^1$ solution to Burger's equation and $(\gamma_0, \gamma_1)$
is a characteristic curve, then $\frac{d}{ds} u(\gamma_0(s), \gamma_1(s)) = 0$. -/
theorem deriv_along_char_eq_zero
    (u : ℝ → ℝ → ℝ) (γ₀ γ₁ : ℝ → ℝ)
    (hu : IsBurgerSolution u)
    (hchar : IsCharacteristicCurve u γ₀ γ₁)
    (hγ₀_diff : Differentiable ℝ γ₀)
    (hγ₁_diff : Differentiable ℝ γ₁)
    (s : ℝ) :
    deriv (fun s => u (γ₀ s) (γ₁ s)) s = 0 := by
  obtain ⟨hC1, hpde⟩ := hu
  obtain ⟨hγ₀_eq, hγ₁_eq⟩ := hchar

  set L := fderiv ℝ (Function.uncurry u) (γ₀ s, γ₁ s)
  have hfderiv : HasFDerivAt (Function.uncurry u) L (γ₀ s, γ₁ s) :=
    (hC1.differentiable_one.differentiableAt).hasFDerivAt

  have hd₀ : HasDerivAt γ₀ 1 s := by
    rw [← hγ₀_eq s]; exact (hγ₀_diff s).hasDerivAt
  have hd₁ : HasDerivAt γ₁ (u (γ₀ s) (γ₁ s)) s := by
    rw [← hγ₁_eq s]; exact (hγ₁_diff s).hasDerivAt

  have hprod : HasDerivAt (fun s => (γ₀ s, γ₁ s)) ((1 : ℝ), u (γ₀ s) (γ₁ s)) s :=
    hd₀.prodMk hd₁
  have hchain : HasDerivAt (Function.uncurry u ∘ fun s => (γ₀ s, γ₁ s))
      (L ((1 : ℝ), u (γ₀ s) (γ₁ s))) s :=
    hfderiv.comp_hasDerivAt s hprod

  have hderiv_val : deriv (fun s => u (γ₀ s) (γ₁ s)) s = L ((1 : ℝ), u (γ₀ s) (γ₁ s)) :=
    (hchain : HasDerivAt (fun s => u (γ₀ s) (γ₁ s)) _ s).deriv
  rw [hderiv_val]

  set c := u (γ₀ s) (γ₁ s)
  have hlin : L ((1 : ℝ), c) = L (1, 0) + c * L (0, 1) := by
    have : ((1 : ℝ), c) = (1 : ℝ) • ((1 : ℝ), (0 : ℝ)) + c • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, one_mul]
  rw [hlin]

  have hL10 : L (1, 0) = deriv (fun t' => u t' (γ₁ s)) (γ₀ s) := by
    have hd : HasDerivAt (fun t' => u t' (γ₁ s)) (L (1, 0)) (γ₀ s) := by
      rw [hasDerivAt_iff_hasFDerivAt]
      convert hfderiv.comp (γ₀ s) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (γ₀ s) (γ₁ s)) using 1
      ext
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul]
    exact hd.deriv.symm
  have hL01 : L (0, 1) = deriv (fun x' => u (γ₀ s) x') (γ₁ s) := by
    have hd : HasDerivAt (fun x' => u (γ₀ s) x') (L (0, 1)) (γ₁ s) := by
      rw [hasDerivAt_iff_hasFDerivAt]
      convert hfderiv.comp (γ₁ s) (hasFDerivAt_prodMk_right (𝕜 := ℝ) (γ₀ s) (γ₁ s)) using 1
      ext
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, smul_eq_mul]
    exact hd.deriv.symm

  rw [hL10, hL01]
  exact hpde (γ₀ s) (γ₁ s)

/-- Proposition 2.0.2: $C^1$ solutions to Burger's equation are constant along
characteristic curves. -/
theorem burger_constant_along_characteristics
    (u : ℝ → ℝ → ℝ) (γ₀ γ₁ : ℝ → ℝ)
    (hu : IsBurgerSolution u)
    (hchar : IsCharacteristicCurve u γ₀ γ₁)
    (hγ₀_diff : Differentiable ℝ γ₀)
    (hγ₁_diff : Differentiable ℝ γ₁)
    (s₁ s₂ : ℝ) :
    u (γ₀ s₁) (γ₁ s₁) = u (γ₀ s₂) (γ₁ s₂) := by
  have hdiff : Differentiable ℝ (fun s => u (γ₀ s) (γ₁ s)) :=
    differentiable_along_char u γ₀ γ₁ hu.1 hγ₀_diff hγ₁_diff
  have hzero : ∀ s, deriv (fun s => u (γ₀ s) (γ₁ s)) s = 0 :=
    fun s => deriv_along_char_eq_zero u γ₀ γ₁ hu hchar hγ₀_diff hγ₁_diff s
  exact is_const_of_deriv_eq_zero hdiff hzero s₁ s₂

end Burger
