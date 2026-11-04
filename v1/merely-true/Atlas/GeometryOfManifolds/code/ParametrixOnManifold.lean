/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.Basic

set_option autoImplicit false

open scoped Manifold

namespace ParametrixOnManifold


/-- A smooth section of a vector bundle $V \to M$ over a manifold $M$, i.e. an element of
$\Gamma(V) = C^\infty(M, V)$. -/
abbrev SmoothSection
    {E_model : Type*} [NormedAddCommGroup E_model] [NormedSpace ℝ E_model]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E_model H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : M → Type*) [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] :=
  ContMDiffSection I F ⊤ V


/-- A family of Sobolev norms $\|\cdot\|_{W^s}$ on smooth sections of a vector bundle over a
compact manifold $M$, indexed by the regularity index $s \in \mathbb{N}$, satisfying
non-negativity, monotonicity in $s$, and the triangle inequality. -/
structure SobolevNormFamily
    {E_model : Type*} [NormedAddCommGroup E_model] [NormedSpace ℝ E_model]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E_model H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
    (FE : Type*) [NormedAddCommGroup FE] [NormedSpace ℝ FE]
    (VE : M → Type*) [TopologicalSpace (Bundle.TotalSpace FE VE)]
    [∀ x : M, TopologicalSpace (VE x)] [FiberBundle FE VE]
    [∀ x, AddCommGroup (VE x)] [∀ x, Module ℝ (VE x)] [VectorBundle ℝ FE VE] where
  norm : ℕ → SmoothSection I M FE VE → ℝ
  norm_nonneg : ∀ (s : ℕ) (σ : SmoothSection I M FE VE), 0 ≤ norm s σ
  norm_mono : ∀ (s t : ℕ) (σ : SmoothSection I M FE VE),
    s ≤ t → norm s σ ≤ norm t σ
  norm_add : ∀ (s : ℕ) (σ τ : SmoothSection I M FE VE),
    norm s (σ + τ) ≤ norm s σ + norm s τ


/-- A linear operator $S$ on $\Gamma(V)$ is a *smoothing operator* if it improves Sobolev
regularity by one degree: for every $s$, there exists $C > 0$ with
$\|S\sigma\|_{W^{s+1}} \leq C \|\sigma\|_{W^s}$. -/
structure IsSmoothingOnManifold
    {E_model : Type*} [NormedAddCommGroup E_model] [NormedSpace ℝ E_model]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E_model H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
    {FE : Type*} [NormedAddCommGroup FE] [NormedSpace ℝ FE]
    {VE : M → Type*} [TopologicalSpace (Bundle.TotalSpace FE VE)]
    [∀ x : M, TopologicalSpace (VE x)] [FiberBundle FE VE]
    [∀ x, AddCommGroup (VE x)] [∀ x, Module ℝ (VE x)] [VectorBundle ℝ FE VE]
    (W : SobolevNormFamily I FE VE)
    (S : SmoothSection I M FE VE →ₗ[ℝ] SmoothSection I M FE VE) where
  regularity_improvement : ∀ (s : ℕ), ∃ (C : ℝ), C > 0 ∧
    ∀ (σ : SmoothSection I M FE VE), W.norm (s + 1) (S σ) ≤ C * W.norm s σ


/-- A linear operator $L : \Gamma(V_E) \to \Gamma(V_F)$ between sections of two vector bundles
on a compact manifold $M$ has a *parametrix* $P : \Gamma(V_F) \to \Gamma(V_E)$ if both
$P \circ L - \mathrm{id}$ and $L \circ P - \mathrm{id}$ are smoothing operators (raising
Sobolev regularity $W^s \to W^{s+1}$). -/
structure HasParametrixOnManifold
    {E_model : Type*} [NormedAddCommGroup E_model] [NormedSpace ℝ E_model]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E_model H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [CompactSpace M] [IsManifold I ⊤ M]

    {FE : Type*} [NormedAddCommGroup FE] [NormedSpace ℝ FE]
    {VE : M → Type*} [TopologicalSpace (Bundle.TotalSpace FE VE)]
    [∀ x : M, TopologicalSpace (VE x)] [FiberBundle FE VE]
    [∀ x, AddCommGroup (VE x)] [∀ x, Module ℝ (VE x)] [VectorBundle ℝ FE VE]

    {FF : Type*} [NormedAddCommGroup FF] [NormedSpace ℝ FF]
    {VF : M → Type*} [TopologicalSpace (Bundle.TotalSpace FF VF)]
    [∀ x : M, TopologicalSpace (VF x)] [FiberBundle FF VF]
    [∀ x, AddCommGroup (VF x)] [∀ x, Module ℝ (VF x)] [VectorBundle ℝ FF VF]

    (L : SmoothSection I M FE VE →ₗ[ℝ] SmoothSection I M FF VF) where
  P : SmoothSection I M FF VF →ₗ[ℝ] SmoothSection I M FE VE
  S_left : SmoothSection I M FE VE →ₗ[ℝ] SmoothSection I M FE VE
  S_right : SmoothSection I M FF VF →ₗ[ℝ] SmoothSection I M FF VF
  W_E : SobolevNormFamily I FE VE
  W_F : SobolevNormFamily I FF VF
  PL_eq : ∀ (σ : SmoothSection I M FE VE), P (L σ) = σ + S_left σ
  LP_eq : ∀ (τ : SmoothSection I M FF VF), L (P τ) = τ + S_right τ
  isSmoothing_left : IsSmoothingOnManifold W_E S_left
  isSmoothing_right : IsSmoothingOnManifold W_F S_right


/-- A linear differential operator $L$ of order $m$ between sections of vector bundles on $M$
is *elliptic* if its principal symbol $\sigma_m(L)(x, \xi) : (V_E)_x \to (V_F)_x$ is a linear
bijection for every $x \in M$ and every nonzero cotangent vector $\xi$, and is homogeneous of
degree $m$ in $\xi$. -/
structure IsEllipticOnManifold
    {E_model : Type*} [NormedAddCommGroup E_model] [NormedSpace ℝ E_model]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E_model H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]

    {FE : Type*} [NormedAddCommGroup FE] [NormedSpace ℝ FE]
    {VE : M → Type*} [TopologicalSpace (Bundle.TotalSpace FE VE)]
    [∀ x : M, TopologicalSpace (VE x)] [FiberBundle FE VE]
    [∀ x, AddCommGroup (VE x)] [∀ x, Module ℝ (VE x)] [VectorBundle ℝ FE VE]

    {FF : Type*} [NormedAddCommGroup FF] [NormedSpace ℝ FF]
    {VF : M → Type*} [TopologicalSpace (Bundle.TotalSpace FF VF)]
    [∀ x : M, TopologicalSpace (VF x)] [FiberBundle FF VF]
    [∀ x, AddCommGroup (VF x)] [∀ x, Module ℝ (VF x)] [VectorBundle ℝ FF VF]
    (L : SmoothSection I M FE VE →ₗ[ℝ] SmoothSection I M FF VF) where
  order : ℕ
  symbol : M → E_model → (FE →ₗ[ℝ] FF)
  elliptic : ∀ (x : M) (ξ : E_model), ξ ≠ 0 → Function.Bijective (symbol x ξ)
  symbol_homogeneous : ∀ (x : M) (t : ℝ) (ξ : E_model) (v : FE),
    symbol x (t • ξ) v = t ^ order • symbol x ξ v

end ParametrixOnManifold
