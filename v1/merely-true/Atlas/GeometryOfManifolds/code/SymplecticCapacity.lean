/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.SymplecticManifolds

set_option autoImplicit false

open DifferentialFormSpace


/-- The symplectic capacity of a ball or cylinder of radius $r$, defined as $\pi r^2$. -/
noncomputable def symplCapacity (r : ℝ) : NNReal :=
  ⟨Real.pi * r ^ 2, mul_nonneg Real.pi_nonneg (sq_nonneg r)⟩


/-- Marker class identifying a symplectic manifold $S$ as the standard symplectic ball $B^{2n}(r)$ of radius $r > 0$. -/
class IsSymplecticBall {Ω : ℕ → Type*} {VF : Type*}
    [DifferentialFormSpace Ω VF] (S : SymplecticManifold Ω VF) where
  radius : ℝ
  halfDim : ℕ
  radius_pos : 0 < radius
  halfDim_pos : 0 < halfDim
  ω_exact : IsExact' VF S.ω
  capacity_val : NNReal
  capacity_eq : capacity_val = symplCapacity radius

/-- Marker class identifying a symplectic manifold $S$ as the standard symplectic cylinder $Z^{2n}(r) = B^2(r) \times \mathbb{R}^{2n-2}$. -/
class IsSymplecticCylinder {Ω : ℕ → Type*} {VF : Type*}
    [DifferentialFormSpace Ω VF] (S : SymplecticManifold Ω VF) where
  radius : ℝ
  halfDim : ℕ
  radius_pos : 0 < radius
  halfDim_pos : 0 < halfDim
  ω_exact : IsExact' VF S.ω
  capacity_val : NNReal
  capacity_eq : capacity_val = symplCapacity radius


/-- A symplectic embedding $\varphi : (S_1, \omega_1) \hookrightarrow (S_2, \omega_2)$: a morphism satisfying $\varphi^*\omega_2 = \omega_1$. -/
structure SymplecticEmbedding
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁] [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    (S₁ : SymplecticManifold Ω₁ VF₁) (S₂ : SymplecticManifold Ω₂ VF₂) where
  toMorphism : DFSMorphism Ω₁ VF₁ Ω₂ VF₂
  pullback_symplectic : toMorphism.pullback S₂.ω = S₁.ω


/-- A symplectic capacity $c$: a monotone invariant assigning $c(S) \in [0, \infty]$ to each symplectic manifold, satisfying $c(B^{2n}(r)) = c(Z^{2n}(r)) = \pi r^2$ (normalization) and $c(S_1) \le c(S_2)$ whenever $S_1$ embeds symplectically into $S_2$. -/
structure SymplecticCapacity
    (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  cap : SymplecticManifold Ω VF → NNReal
  monotonicity :
    ∀ (S₁ S₂ : SymplecticManifold Ω VF)
    (_φ : SymplecticEmbedding S₁ S₂),
    cap S₁ ≤ cap S₂
  normalization_ball :
    ∀ (S : SymplecticManifold Ω VF)
    [hBall : IsSymplecticBall S],
    cap S = symplCapacity hBall.radius
  normalization_cylinder :
    ∀ (S : SymplecticManifold Ω VF)
    [hCyl : IsSymplecticCylinder S],
    cap S = symplCapacity hCyl.radius


/-- The capacity of a symplectic ball equals its stored capacity value: $c(B^{2n}(r)) = \pi r^2$. -/
theorem SymplecticCapacity.cap_eq_ball_capacity_val
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    (c : SymplecticCapacity Ω VF) (S : SymplecticManifold Ω VF)
    [hBall : IsSymplecticBall S] :
    c.cap S = hBall.capacity_val := by
  rw [hBall.capacity_eq]
  exact c.normalization_ball S

/-- The capacity of a symplectic cylinder equals its stored capacity value: $c(Z^{2n}(r)) = \pi r^2$. -/
theorem SymplecticCapacity.cap_eq_cylinder_capacity_val
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    (c : SymplecticCapacity Ω VF) (S : SymplecticManifold Ω VF)
    [hCyl : IsSymplecticCylinder S] :
    c.cap S = hCyl.capacity_val := by
  rw [hCyl.capacity_eq]
  exact c.normalization_cylinder S


/-- Numerical form of the ball normalization: $c(B^{2n}(r)) = \pi r^2$ as a real number. -/
theorem SymplecticCapacity.cap_ball_eq_pi_rsq
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    (c : SymplecticCapacity Ω VF) (S : SymplecticManifold Ω VF)
    [hBall : IsSymplecticBall S] :
    (c.cap S : ℝ) = Real.pi * hBall.radius ^ 2 := by
  have h := c.normalization_ball S
  rw [h]
  rfl

/-- Numerical form of the cylinder normalization: $c(Z^{2n}(r)) = \pi r^2$ as a real number. -/
theorem SymplecticCapacity.cap_cylinder_eq_pi_rsq
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    (c : SymplecticCapacity Ω VF) (S : SymplecticManifold Ω VF)
    [hCyl : IsSymplecticCylinder S] :
    (c.cap S : ℝ) = Real.pi * hCyl.radius ^ 2 := by
  have h := c.normalization_cylinder S
  rw [h]
  rfl
