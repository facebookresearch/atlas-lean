/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.DifferentialForms
import Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra

set_option autoImplicit false

open DifferentialFormSpace


/-- Pullback commutes with negation: $\varphi^*(-\alpha) = -\varphi^*\alpha$. -/
lemma pullback_neg {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁] [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    (φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂) {p : ℕ} (α : Ω₂ p) :
    φ.pullback (-α) = -(φ.pullback α) := by
  have h := φ.pullback_smul (-1 : ℝ) α
  simp only [neg_smul, one_smul] at h
  exact h

/-- Pullback is additive on differences: $\varphi^*(\alpha - \beta) = \varphi^*\alpha - \varphi^*\beta$. -/
lemma pullback_sub {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁] [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    (φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂) {p : ℕ} (α β : Ω₂ p) :
    φ.pullback (α - β) = φ.pullback α - φ.pullback β := by
  rw [sub_eq_add_neg, φ.pullback_add, pullback_neg, ← sub_eq_add_neg]


/-- A **symplectic manifold** (Definition 7): a $2$-form $\omega \in \Omega^2(M)$ that is closed
($d\omega = 0$) and non-degenerate (the contraction map $X \mapsto \iota_X \omega$ is injective). -/
structure SymplecticManifold (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  ω : Ω 2
  closed : inst.d ω = 0
  nondegenerate : Function.Injective (fun (X : VF) => inst.ι X ω)


/-- Records that a differential form space carries a positive half-dimension $n > 0$, so the
ambient symplectic manifold has total dimension $2n$. -/
class SymplecticManifoldDim (Ω : ℕ → Type*) (VF : Type*)
    [DifferentialFormSpace Ω VF] where
  n : ℕ
  n_pos : 0 < n

/-- Marks a $2n$-dimensional symplectic differential form space as **compact symplectic**: the
symplectic form $\omega$ is not exact and there is a top-degree volume form $\omega^n$ which is
also not exact. This abstracts the cohomological obstructions that hold on compact symplectic
manifolds. -/
class IsCompactSymplectic (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] extends SymplecticManifoldDim Ω VF where
  symplectic_not_exact : (S : SymplecticManifold Ω VF) → ¬ IsExact' VF S.ω
  vol : (S : SymplecticManifold Ω VF) → Ω (2 * toSymplecticManifoldDim.n - 1 + 1)
  volume_not_exact : (S : SymplecticManifold Ω VF) →
    ¬ (∃ β : Ω (2 * toSymplecticManifoldDim.n - 1),
      inst.d β = vol S)


/-- A **symplectomorphism** (Definition 8): an invertible morphism of differential form spaces
$\varphi : (M_1, \omega_1) \to (M_2, \omega_2)$ satisfying $\varphi^* \omega_2 = \omega_1$. Encoded
with explicit two-sided inverse data at the level of pullbacks. -/
structure Symplectomorphism
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁] [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    (S₁ : SymplecticManifold Ω₁ VF₁) (S₂ : SymplecticManifold Ω₂ VF₂) where
  toMorphism : DFSMorphism Ω₁ VF₁ Ω₂ VF₂
  invMorphism : DFSMorphism Ω₂ VF₂ Ω₁ VF₁
  left_inv : ∀ {p : ℕ} (β : Ω₂ p), invMorphism.pullback (toMorphism.pullback β) = β
  right_inv : ∀ {p : ℕ} (α : Ω₁ p), toMorphism.pullback (invMorphism.pullback α) = α
  pullback_symplectic : toMorphism.pullback S₂.ω = S₁.ω


/-- A submanifold $W \hookrightarrow M$ is **symplectic** when the pullback $i^*\omega$ remains
non-degenerate on $W$, i.e. $X \mapsto \iota_X (i^*\omega)$ is injective on $\mathfrak{X}(W)$. -/
structure IsSymplecticSubmanifold
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_W : ℕ → Type*} {VF_W : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_W : DifferentialFormSpace Ω_W VF_W]
    (S : SymplecticManifold Ω_M VF_M)
    (i : DFSMorphism Ω_W VF_W Ω_M VF_M) : Prop where
  restriction_nondegenerate :
    Function.Injective (fun (X : VF_W) => inst_W.ι X (i.pullback S.ω))

/-- A submanifold $L \hookrightarrow M$ is **Lagrangian** when $i^*\omega = 0$ and $\dim L =
\tfrac{1}{2}\dim M$, i.e. $L$ is isotropic of maximal dimension. -/
structure IsLagrangianSubmanifold
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_L : ℕ → Type*} {VF_L : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_L : DifferentialFormSpace Ω_L VF_L]
    (S : SymplecticManifold Ω_M VF_M)
    (i : DFSMorphism Ω_L VF_L Ω_M VF_M)
    (dimM : ℕ) (dimL : ℕ) : Prop where
  restriction_zero : i.pullback S.ω = 0
  half_dim : 2 * dimL = dimM


/-- Axiomatic interface for the **cotangent bundle** $T^*X$ of a manifold $X$: equips $T^*X$ with
the tautological Liouville 1-form $\theta$, the canonical symplectic form $\omega = d\theta$, and a
zero section $X \hookrightarrow T^*X$ along which $\theta$ pulls back to $0$. -/
class CotangentBundleDFS
    (Ω_X : ℕ → Type*) (VF_X : Type*)
    (Ω_TX : ℕ → Type*) (VF_TX : Type*)
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_TX : DifferentialFormSpace Ω_TX VF_TX] where
  dimX : ℕ
  dimX_pos : 0 < dimX
  liouville : Ω_TX 1
  canonical_symplectic : SymplecticManifold Ω_TX VF_TX
  symplectic_eq_d_liouville : canonical_symplectic.ω = inst_TX.d liouville
  zeroSection : DFSMorphism Ω_X VF_X Ω_TX VF_TX
  liouville_zero_section : zeroSection.pullback liouville = (0 : Ω_X 1)


/-- Auxiliary setup for the graph $\Gamma_\varphi \subset M_1 \times M_2$ of a map
$\varphi : M_1 \to M_2$ between symplectic manifolds: projections $\pi_1, \pi_2$, an embedding
$\gamma : M_1 \to \Gamma_\varphi$, and the compatibility $\gamma^*\pi_1^* = \mathrm{id}$,
$\gamma^*\pi_2^* = \varphi^*$. -/
structure GraphSetup
    (Ω₁ : ℕ → Type*) (VF₁ : Type*)
    (Ω₂ : ℕ → Type*) (VF₂ : Type*)
    (Ω_P : ℕ → Type*) (VF_P : Type*)
    [inst₁ : DifferentialFormSpace Ω₁ VF₁]
    [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    [inst_P : DifferentialFormSpace Ω_P VF_P]
    (S₁ : SymplecticManifold Ω₁ VF₁)
    (S₂ : SymplecticManifold Ω₂ VF₂) where
  π₁ : DFSMorphism Ω_P VF_P Ω₁ VF₁
  π₂ : DFSMorphism Ω_P VF_P Ω₂ VF₂
  φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂
  γ : DFSMorphism Ω₁ VF₁ Ω_P VF_P
  dimM₁ : ℕ
  dimM₂ : ℕ
  dim_eq : dimM₁ = dimM₂
  γ_π₁ : ∀ {p : ℕ} (α : Ω₁ p), γ.pullback (π₁.pullback α) = α
  γ_π₂ : ∀ {p : ℕ} (β : Ω₂ p), γ.pullback (π₂.pullback β) = φ.pullback β

/-- If $\varphi^* \omega_2 = \omega_1$ (i.e. $\varphi$ is a symplectomorphism), then the graph
$\Gamma_\varphi$ is isotropic for $\pi_1^*\omega_1 - \pi_2^*\omega_2$: the pullback of this
difference along $\gamma$ vanishes. -/
theorem graph_lagrangian_of_symplectomorphism
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    {Ω_P : ℕ → Type*} {VF_P : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁]
    [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    [inst_P : DifferentialFormSpace Ω_P VF_P]
    {S₁ : SymplecticManifold Ω₁ VF₁}
    {S₂ : SymplecticManifold Ω₂ VF₂}
    (G : GraphSetup Ω₁ VF₁ Ω₂ VF₂ Ω_P VF_P S₁ S₂)
    (hφ : G.φ.pullback S₂.ω = S₁.ω) :
    G.γ.pullback (G.π₁.pullback S₁.ω - G.π₂.pullback S₂.ω) = (0 : Ω₁ 2) := by
  rw [pullback_sub (inst₂ := inst_P), G.γ_π₁, G.γ_π₂, hφ, sub_self]

/-- Converse: if $\gamma^*(\pi_1^*\omega_1 - \pi_2^*\omega_2) = 0$ on the graph, then
$\varphi^*\omega_2 = \omega_1$, so $\varphi$ is a symplectomorphism. -/
theorem symplectomorphism_of_graph_lagrangian
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    {Ω_P : ℕ → Type*} {VF_P : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁]
    [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    [inst_P : DifferentialFormSpace Ω_P VF_P]
    {S₁ : SymplecticManifold Ω₁ VF₁}
    {S₂ : SymplecticManifold Ω₂ VF₂}
    (G : GraphSetup Ω₁ VF₁ Ω₂ VF₂ Ω_P VF_P S₁ S₂)
    (hLag : G.γ.pullback (G.π₁.pullback S₁.ω - G.π₂.pullback S₂.ω) = (0 : Ω₁ 2)) :
    G.φ.pullback S₂.ω = S₁.ω := by
  rw [pullback_sub (inst₂ := inst_P), G.γ_π₁, G.γ_π₂] at hLag
  exact (sub_eq_zero.mp hLag).symm
