/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Analysis.Complex.Basic

noncomputable section

open scoped Manifold
open Bundle


/-- Typeclass wrapper recording that a vector bundle $V \to M$ has smooth transition functions (modeled in the DFS framework). -/
class SmoothVectorBundleDFS
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM]
    (I : ModelWithCorners ℝ EM HM)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HM M]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : M → Type*)
    [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
    [VectorBundle ℝ F V] : Prop where
  smoothTransitions : ContMDiffVectorBundle ⊤ F V I


/-- The space of (smooth) sections of a vector bundle $V \to M$, identified with the dependent function type $\prod_{x \in M} V_x$. -/
def SmoothSections {M : Type*} (V : M → Type*) : Type _ := ∀ x : M, V x

namespace SmoothSections

/-- Sections form an abelian group under pointwise addition. -/
instance instAddCommGroup {M : Type*} {V : M → Type*}
    [∀ x, AddCommGroup (V x)] : AddCommGroup (SmoothSections V) :=
  Pi.addCommGroup

/-- Sections form a real vector space under pointwise scalar multiplication. -/
instance instModule {M : Type*} {V : M → Type*}
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] :
    Module ℝ (SmoothSections V) :=
  Pi.module _ _ _

/-- Evaluation of a section $\sigma$ at a point $x \in M$. -/
def eval {M : Type*} {V : M → Type*} (σ : SmoothSections V) (x : M) : V x := σ x

/-- The zero section of a vector bundle. -/
instance instZero {M : Type*} {V : M → Type*}
    [∀ x, Zero (V x)] : Zero (SmoothSections V) :=
  Pi.instZero

end SmoothSections


/-- A connection $\nabla$ on a vector bundle $V \to M$: a covariant derivative sending a section $\sigma$ and a tangent vector $X_x$ to $\nabla_X \sigma \in V_x$. -/
structure ConnectionDFS
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM]
    (I : ModelWithCorners ℝ EM HM)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HM M]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul ℝ (V x)]
    [FiberBundle F V] where
  nabla : (∀ x : M, V x) → (∀ x : M, TangentSpace I x →L[ℝ] V x)
  isCovariantDerivative : IsCovariantDerivativeOn F nabla

namespace ConnectionDFS

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V]

/-- Apply a connection: $(\nabla_X \sigma)_x = \mathtt{conn.apply}\ \sigma\ x\ X$. -/
def apply (conn : ConnectionDFS I M F V) (σ : ∀ x : M, V x) (x : M)
    (X : TangentSpace I x) : V x :=
  conn.nabla σ x X

/-- The difference $\nabla_1 - \nabla_2$ of two connections (an $\mathrm{End}(V)$-valued $1$-form). -/
def difference (conn₁ conn₂ : ConnectionDFS I M F V) :
    (∀ x : M, V x) → (∀ x : M, TangentSpace I x →L[ℝ] V x) :=
  fun σ x => conn₁.nabla σ x - conn₂.nabla σ x

end ConnectionDFS


/-- Data for the normal bundle of an embedding $\iota : N \hookrightarrow M$: fibers $\mathcal{N}_x$, module structure, and the normal rank. -/
structure NormalBundleData
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN]
    (IN : ModelWithCorners ℝ EN HN)
    (N : Type*) [TopologicalSpace N] [ChartedSpace HN N]
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM]
    (IM : ModelWithCorners ℝ EM HM)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HM M] where
  ι : N → M
  NormalFiber : N → Type*
  instACG : ∀ x, AddCommGroup (NormalFiber x)
  instMod : ∀ x, Module ℝ (NormalFiber x)
  normalRank : ℕ

namespace NormalBundleData

attribute [instance] NormalBundleData.instACG NormalBundleData.instMod

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

end NormalBundleData


/-- A $\operatorname{Spin}^{\mathbb{C}}$ structure on $M$: complex spinor bundles $W^+, W^-$ with Clifford multiplication maps $\gamma_{\pm} : TM \otimes W^{\pm} \to W^{\mp}$ and first Chern class $c_1$ of the determinant line bundle. -/
structure SpinCStructureDFS
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM]
    (I : ModelWithCorners ℝ EM HM)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HM M]
    [IsManifold I ⊤ M] where
  SpinorPlusFiber : M → Type*
  SpinorMinusFiber : M → Type*
  instACG_plus : ∀ x, AddCommGroup (SpinorPlusFiber x)
  instMod_plus : ∀ x, Module ℂ (SpinorPlusFiber x)
  instACG_minus : ∀ x, AddCommGroup (SpinorMinusFiber x)
  instMod_minus : ∀ x, Module ℂ (SpinorMinusFiber x)
  γ_plus_to_minus : ∀ x, TangentSpace I x → (SpinorPlusFiber x →ₗ[ℂ] SpinorMinusFiber x)
  γ_minus_to_plus : ∀ x, TangentSpace I x → (SpinorMinusFiber x →ₗ[ℂ] SpinorPlusFiber x)
  c₁ : ℤ

namespace SpinCStructureDFS

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I ⊤ M]

/-- The positive spinor fiber $W^+_x$ inherits an abelian group structure. -/
instance instACGPlus (spinc : SpinCStructureDFS I M) (x : M) :
    AddCommGroup (spinc.SpinorPlusFiber x) := spinc.instACG_plus x

/-- The positive spinor fiber $W^+_x$ is a complex vector space. -/
instance instModPlus (spinc : SpinCStructureDFS I M) (x : M) :
    Module ℂ (spinc.SpinorPlusFiber x) := spinc.instMod_plus x

/-- The negative spinor fiber $W^-_x$ inherits an abelian group structure. -/
instance instACGMinus (spinc : SpinCStructureDFS I M) (x : M) :
    AddCommGroup (spinc.SpinorMinusFiber x) := spinc.instACG_minus x

/-- The negative spinor fiber $W^-_x$ is a complex vector space. -/
instance instModMinus (spinc : SpinCStructureDFS I M) (x : M) :
    Module ℂ (spinc.SpinorMinusFiber x) := spinc.instMod_minus x

/-- Sections $\Gamma(W^+)$ of the positive spinor bundle. -/
def SectionsPlus (spinc : SpinCStructureDFS I M) : Type _ :=
  SmoothSections spinc.SpinorPlusFiber

/-- Sections $\Gamma(W^-)$ of the negative spinor bundle. -/
def SectionsMinus (spinc : SpinCStructureDFS I M) : Type _ :=
  SmoothSections spinc.SpinorMinusFiber

end SpinCStructureDFS


end
