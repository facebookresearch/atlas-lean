/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.TitsCone
import Atlas.Buildings.code.ChamberComplex.Basic
import Atlas.Buildings.code.ChamberComplex.CoxeterComplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators

namespace GeometricRealization

variable {V : Type*} [DecidableEq V] [Fintype V] [Nonempty V]

/-- A **point** of the geometric realization $|\Delta|$ of a simplicial complex $\Delta$: a barycentric
weighting of vertices that sums to $1$ and whose support lies in some face of $\Delta$. -/
structure Point (Δ : SimplicialComplex V) where
  wt : V → ℝ
  wt_nonneg : ∀ v, wt v ≥ 0
  wt_sum : ∑ v : V, wt v = 1
  support_in_face : ∃ σ ∈ Δ.faces, ∀ v, wt v ≠ 0 → v ∈ σ

/-- $\ell^\infty$ distance between two points in $|\Delta|$: the supremum of $|p_v - q_v|$ over $v$. -/
noncomputable def dist {Δ : SimplicialComplex V} (p q : Point Δ) : ℝ :=
  Finset.univ.sup' ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    (fun v => |p.wt v - q.wt v|)

/-- The canonical embedding of a vertex $v$ as the corresponding $\delta_v$-point of $|\Delta|$. -/
noncomputable def vertexEmbedding (Δ : SimplicialComplex V) (v : V)
    (hv : {v} ∈ Δ.faces) : Point Δ where
  wt := fun w => if w = v then 1 else 0
  wt_nonneg := by intro w; split_ifs <;> norm_num
  wt_sum := by simp [Finset.sum_ite_eq']
  support_in_face := by
    refine ⟨{v}, hv, fun w hw => ?_⟩
    simp only [Finset.mem_singleton]
    by_contra h
    apply hw
    simp only [ite_eq_right_iff]
    intro heq
    exact absurd heq h

/-- The support of a point $p \in |\Delta|$: the (necessarily finite) set $\{v : p_v \ne 0\}$. -/
def support {Δ : SimplicialComplex V} (p : Point Δ) : Finset V :=
  Finset.univ.filter (fun v => p.wt v ≠ 0)

/-- Vertex-realization: given a vertex map $i : V \to Z$ into an $\mathbb R$-module, extend to the
geometric realization $|\Delta| \to Z$ by barycentric combinations $p \mapsto \sum_v p_v \cdot i(v)$. -/
noncomputable def vertexRealizationMap {Δ : SimplicialComplex V}
    {Z : Type*} [AddCommMonoid Z] [Module ℝ Z]
    (i : V → Z) (p : Point Δ) : Z :=
  ∑ v : V, p.wt v • i v

end GeometricRealization

/-- An abstract geometric realization of a Coxeter complex $(W, S)$: a topological space carrier
together with a $W$-indexed family of "chamber" subsets and a fundamental domain. -/
structure CoxeterComplexGeometricRealization (W : Type*) [Group W] (S : Set W) where
  carrier : Type*
  [topSpace : TopologicalSpace carrier]
  chamberMap : W → Set carrier
  fundamentalDomain : Set carrier

attribute [instance] CoxeterComplexGeometricRealization.topSpace

/-- An **affine** geometric realization: an action of $W$ by Euclidean transformations of
$\mathbb R^\iota$, together with a fundamental chamber, its $W$-translates, and the underlying
hyperplane arrangement. -/
structure AffineGeometricRealization (W : Type*) [Group W] (S : Set W)
    (ι : Type*) [Fintype ι] where
  action : W → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι
  action_mul : ∀ w₁ w₂ : W, ∀ x, action (w₁ * w₂) x = action w₁ (action w₂ x)
  action_one : ∀ x, action 1 x = x
  fundamentalChamber : Set (EuclideanSpace ℝ ι)
  chamber (w : W) : Set (EuclideanSpace ℝ ι) := action w '' fundamentalChamber
  hyperplanes : Set (Set (EuclideanSpace ℝ ι))

/-- Forgetting the linear/Euclidean structure: every affine geometric realization gives an abstract
geometric realization with the same chambers and fundamental domain. -/
def AffineGeometricRealization.toCoxeterComplex {W : Type*} [Group W] {S : Set W}
    {ι : Type*} [Fintype ι] (A : AffineGeometricRealization W S ι) :
    CoxeterComplexGeometricRealization W S where
  carrier := EuclideanSpace ℝ ι
  chamberMap := fun w => A.action w '' A.fundamentalChamber
  fundamentalDomain := A.fundamentalChamber

end
