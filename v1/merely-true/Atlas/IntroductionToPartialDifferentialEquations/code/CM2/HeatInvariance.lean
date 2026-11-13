/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.FDeriv.Basic

open Finset

noncomputable section

namespace HeatEquationInvariance

/-- The (spatial) Laplacian of $f : \mathbb{R}^n \to \mathbb{R}$ at $x$, defined as
$\Delta f(x) = \sum_{i=1}^{n} \partial_i^2 f(x)$. -/
def laplacian {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, deriv (fun h => deriv (fun xi => f (Function.update x i xi)) (x i + h)) 0

/-- The heat operator $\partial_t u - D\,\Delta u$ applied to $u$ at $(t, x)$,
where $D > 0$ is the diffusion constant. -/
def heatOperator {n : ℕ} (D : ℝ) (u : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun s => u s x) t - D * laplacian (u t) x

/-- Constants pull out of the time derivative: $\frac{d}{dt}(A f(t)) = A f'(t)$. -/
theorem deriv_const_mul_fn (A : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    deriv (fun s => A * f s) t = A * deriv f t :=
  deriv_const_mul_field A

/-- Linearity of the Laplacian under scalar multiplication: $\Delta(A f) = A\,\Delta f$. -/
theorem laplacian_const_mul {n : ℕ} (A : ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    laplacian (fun y => A * f y) x = A * laplacian f x := by
  unfold laplacian
  simp_rw [deriv_const_mul_field A]
  rw [← Finset.mul_sum]

/-- Time-shift identity for the time derivative:
$\partial_t [u(t - t_0, x)] = (\partial_t u)(t - t_0, x)$. -/
theorem deriv_time_translate {n : ℕ} (u : ℝ → (Fin n → ℝ) → ℝ)
    (t₀ t : ℝ) (x : Fin n → ℝ) :
    deriv (fun s => u (s - t₀) x) t = deriv (fun s => u s x) (t - t₀) :=
  deriv_comp_sub_const (fun s => u s x) t₀ t

/-- Spatial translation commutes with the Laplacian:
$\Delta(f(\cdot - x_0))(x) = (\Delta f)(x - x_0)$. -/
theorem laplacian_translate {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x₀ x : Fin n → ℝ) :
    laplacian (fun y => f (y - x₀)) x = laplacian f (x - x₀) := by
  unfold laplacian
  congr 1
  ext i
  have key : ∀ xi, Function.update x i xi - x₀ = Function.update (x - x₀) i (xi - x₀ i) := by
    intro xi
    ext j
    simp [Function.update, Pi.sub_apply]
    split <;> simp_all
  simp_rw [key]
  have key2 : ∀ h, deriv (fun xi => f (Function.update (x - x₀) i (xi - x₀ i))) (x i + h)
      = deriv (fun xi => f (Function.update (x - x₀) i xi)) (x i + h - x₀ i) := by
    intro h
    exact deriv_comp_sub_const (fun xi => f (Function.update (x - x₀) i xi)) (x₀ i) (x i + h)
  simp_rw [key2]
  congr 1
  ext h
  congr 1
  simp [Pi.sub_apply]
  ring

/-- Parabolic dilation in time: $\partial_t [u(\lambda^2 t, x)] = \lambda^2 (\partial_t u)(\lambda^2 t, x)$. -/
theorem deriv_time_dilate {n : ℕ} (u : ℝ → (Fin n → ℝ) → ℝ)
    (lam t : ℝ) (x : Fin n → ℝ) :
    deriv (fun s => u (lam ^ 2 * s) x) t = lam ^ 2 * deriv (fun s => u s x) (lam ^ 2 * t) := by
  have := deriv_comp_mul_left (lam ^ 2) (fun s => u s x) t
  simp [smul_eq_mul] at this
  exact this

/-- Spatial dilation scales the Laplacian by $\lambda^2$:
$\Delta(f(\lambda \cdot))(x) = \lambda^2 (\Delta f)(\lambda x)$. -/
theorem laplacian_dilate {n : ℕ} (f : (Fin n → ℝ) → ℝ) (lam : ℝ) (x : Fin n → ℝ) :
    laplacian (fun y => f (lam • y)) x = lam ^ 2 * laplacian f (lam • x) := by
  unfold laplacian
  rw [Finset.mul_sum]
  congr 1
  ext i
  have smul_update : ∀ xi, lam • Function.update x i xi = Function.update (lam • x) i (lam * xi) := by
    intro xi; ext j; simp [Function.update, Pi.smul_apply, smul_eq_mul]
  simp_rw [smul_update]
  have inner : ∀ h,
      deriv (fun xi => f (Function.update (lam • x) i (lam * xi))) (x i + h) =
      lam * deriv (fun xi => f (Function.update (lam • x) i xi)) (lam * (x i + h)) := by
    intro h
    have := @deriv_comp_mul_left ℝ ℝ _ _ _ lam (fun xi => f (Function.update (lam • x) i xi)) (x i + h)
    simp [smul_eq_mul] at this; exact this
  simp_rw [inner]
  have shift : ∀ h, lam * (x i + h) = (lam • x) i + lam * h := by
    intro h; simp [Pi.smul_apply, smul_eq_mul, mul_add]
  simp_rw [shift]
  set g := fun xi => f (Function.update (lam • x) i xi)
  set G := fun h => deriv g ((lam • x) i + h)
  conv_lhs =>
    arg 1; ext h
    rw [show lam * G (lam * h) = lam * (G ∘ (lam * ·)) h from by simp [Function.comp]]
  rw [deriv_const_mul_field lam]
  have comp_unfold : G ∘ (lam * ·) = fun h => G (lam * h) := by ext; simp [Function.comp]
  rw [comp_unfold]
  have outer := @deriv_comp_mul_left ℝ ℝ _ _ _ lam G 0
  simp [smul_eq_mul] at outer
  rw [outer]
  ring

/-- Translation invariance of solutions to the heat equation (Lemma 2.0.2, first part):
if $u$ solves $u_t - D \Delta u = 0$, then so does $A\,u(t - t_0, x - x_0)$ for any constants
$A, t_0 \in \mathbb{R}$ and $x_0 \in \mathbb{R}^n$. -/
theorem heat_translation_invariance {n : ℕ} {D : ℝ} (_hD : D > 0)
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (hu : ∀ t x, heatOperator D u t x = 0)
    (A t₀ : ℝ) (x₀ : Fin n → ℝ) :
    ∀ t x, heatOperator D (fun t x => A * u (t - t₀) (x - x₀)) t x = 0 := by
  intro t x
  unfold heatOperator


  rw [deriv_const_mul_fn A (fun s => u (s - t₀) (x - x₀)) t]
  rw [deriv_time_translate u t₀ t (x - x₀)]


  rw [laplacian_const_mul A (fun y => u (t - t₀) (y - x₀)) x]
  rw [laplacian_translate (u (t - t₀)) x₀ x]


  have h := hu (t - t₀) (x - x₀)
  unfold heatOperator at h
  linear_combination A * h

/-- Parabolic dilation invariance of solutions to the heat equation (Lemma 2.0.2, second part):
if $u$ solves $u_t - D \Delta u = 0$, then so does $A\,u(\lambda^2 t, \lambda x)$
for any $A \in \mathbb{R}$ and $\lambda > 0$. -/
theorem heat_parabolic_dilation {n : ℕ} {D : ℝ} (_hD : D > 0)
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (hu : ∀ t x, heatOperator D u t x = 0)
    (A lam : ℝ) (_hlam : lam > 0) :
    ∀ t x, heatOperator D (fun t x => A * u (lam ^ 2 * t) (lam • x)) t x = 0 := by
  intro t x
  unfold heatOperator


  rw [deriv_const_mul_fn A (fun s => u (lam ^ 2 * s) (lam • x)) t]
  rw [deriv_time_dilate u lam t (lam • x)]


  rw [laplacian_const_mul A (fun y => u (lam ^ 2 * t) (lam • y)) x]
  rw [laplacian_dilate (u (lam ^ 2 * t)) lam x]


  have h := hu (lam ^ 2 * t) (lam • x)
  unfold heatOperator at h
  linear_combination A * lam ^ 2 * h

/-- Lemma 2.0.2 (combined): solutions to the heat equation are invariant under
amplification combined with translations and parabolic dilations. -/
theorem heat_equation_invariance {n : ℕ} {D : ℝ} (hD : D > 0)
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (hu : ∀ t x, heatOperator D u t x = 0) :
    (∀ (A t₀ : ℝ) (x₀ : Fin n → ℝ),
      ∀ t x, heatOperator D (fun t x => A * u (t - t₀) (x - x₀)) t x = 0) ∧
    (∀ (A lam : ℝ) (_hlam : lam > 0),
      ∀ t x, heatOperator D (fun t x => A * u (lam ^ 2 * t) (lam • x)) t x = 0) :=
  ⟨fun A t₀ x₀ => heat_translation_invariance hD u hu A t₀ x₀,
   fun A lam hlam => heat_parabolic_dilation hD u hu A lam hlam⟩

end HeatEquationInvariance

end
