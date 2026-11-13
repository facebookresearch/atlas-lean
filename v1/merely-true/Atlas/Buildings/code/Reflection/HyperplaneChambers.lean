/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic

open scoped InnerProductSpace
open Set

noncomputable section

/-- An affine hyperplane $H = \{x ∈ E : ⟨n, x⟩ = c\}$ specified by a nonzero normal
vector $n$ and an offset $c$. -/
structure AffineHyperplane (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  normal : E
  offset : ℝ
  normal_ne_zero : normal ≠ 0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineHyperplane

/-- The underlying set $\{x : ⟨n, x⟩ = c\}$ of the affine hyperplane. -/
def carrier (h : AffineHyperplane E) : Set E :=
  {x : E | ⟪h.normal, x⟫_ℝ = h.offset}

/-- The open positive half-space $\{x : ⟨n, x⟩ > c\}$. -/
def positiveHalfSpace (h : AffineHyperplane E) : Set E :=
  {x : E | ⟪h.normal, x⟫_ℝ > h.offset}

/-- The open negative half-space $\{x : ⟨n, x⟩ < c\}$. -/
def negativeHalfSpace (h : AffineHyperplane E) : Set E :=
  {x : E | ⟪h.normal, x⟫_ℝ < h.offset}

/-- The hyperplane $h$ *separates* $x$ and $y$ if they lie in opposite open half-spaces. -/
def Separates (h : AffineHyperplane E) (x y : E) : Prop :=
  (⟪h.normal, x⟫_ℝ > h.offset ∧ ⟪h.normal, y⟫_ℝ < h.offset) ∨
  (⟪h.normal, x⟫_ℝ < h.offset ∧ ⟪h.normal, y⟫_ℝ > h.offset)

/-- $η$ is a *wall* of $C$ if some open neighborhood of a point of $η$ meets $η$ inside the
closure of $C$. -/
def IsWall (η : AffineHyperplane E) (C : Set E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ (U ∩ η.carrier).Nonempty ∧ U ∩ η.carrier ⊆ closure C

/-- A canonical base point of $η$: the orthogonal projection of $0$ onto $η$. -/
def basePoint (h : AffineHyperplane E) : E :=
  (h.offset / ⟪h.normal, h.normal⟫_ℝ) • h.normal

/-- The direction subspace (parallel translate to the origin) of $η$, equal to $n^⊥$. -/
def direction (h : AffineHyperplane E) : Submodule ℝ E :=
  (Submodule.span ℝ {h.normal})ᗮ

/-- The base point lies on the hyperplane. -/
lemma basePoint_mem_carrier (h : AffineHyperplane E) : h.basePoint ∈ h.carrier := by
  simp only [basePoint, carrier, Set.mem_setOf_eq, inner_smul_right, real_inner_self_eq_norm_sq]
  exact div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr h.normal_ne_zero))

/-- The affine hyperplane viewed as a Mathlib `AffineSubspace`. -/
def toAffineSubspace [CompleteSpace E] (h : AffineHyperplane E) : AffineSubspace ℝ E :=
  { carrier := h.carrier
    smul_vsub_vadd_mem := by
      intro c x y z hx hy hz
      simp only [carrier, Set.mem_setOf_eq] at *
      simp only [vadd_eq_add, vsub_eq_sub,
        inner_add_right, inner_sub_right, inner_smul_right]
      rw [hx, hy, hz]; ring }

/-- The affine subspace associated to a hyperplane is nonempty (it contains the base
point). -/
instance instNonemptyToAffineSubspace [CompleteSpace E] (h : AffineHyperplane E) :
    Nonempty h.toAffineSubspace :=
  ⟨⟨h.basePoint, h.basePoint_mem_carrier⟩⟩

/-- The Euclidean reflection $E ≃ᵃⁱ E$ across the affine hyperplane $η$. -/
def reflectionMap [CompleteSpace E] [FiniteDimensional ℝ E]
    (h : AffineHyperplane E) : E ≃ᵃⁱ[ℝ] E :=
  EuclideanGeometry.reflection h.toAffineSubspace

end AffineHyperplane

/-- A hyperplane arrangement on $E$: simply a set of affine hyperplanes. -/
structure HyperplaneArrangement (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  hyperplanes : Set (AffineHyperplane E)

namespace HyperplaneArrangement

/-- The union $\bigcup_{η ∈ \mathcal A} η$ of all hyperplanes in the arrangement. -/
def unionSet (arr : HyperplaneArrangement E) : Set E :=
  ⋃ h ∈ arr.hyperplanes, h.carrier

/-- The complement of the arrangement: points lying on no hyperplane. -/
def complement (arr : HyperplaneArrangement E) : Set E :=
  Set.univ \ arr.unionSet

/-- An arrangement is *locally finite* if around every point only finitely many
hyperplanes meet a small open ball. -/
def IsLocallyFinite (arr : HyperplaneArrangement E) : Prop :=
  ∀ x : E, ∃ ε > 0, Set.Finite {h ∈ arr.hyperplanes |
    (Metric.ball x ε ∩ h.carrier).Nonempty}

/-- A chamber of an arrangement: a maximal connected subset of the complement of all
hyperplanes. -/
structure Chamber (arr : HyperplaneArrangement E) where
  set : Set E
  subset_complement : set ⊆ arr.complement
  isConnected : IsConnected set
  is_maximal : ∀ S : Set E, S ⊆ arr.complement → IsConnected S → set ⊆ S → S ⊆ set

/-- Two points are *separated by the arrangement* if some hyperplane separates them. -/
def SeparatedBy (arr : HyperplaneArrangement E) (x y : E) : Prop :=
  ∃ h ∈ arr.hyperplanes, h.Separates x y

end HyperplaneArrangement

/-- Open half-spaces are convex. -/
theorem HalfSpaceConvex (h : AffineHyperplane E) : Convex ℝ h.positiveHalfSpace := by
  intro x hx y hy a b ha hb hab
  simp only [AffineHyperplane.positiveHalfSpace, mem_setOf_eq] at *
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp at hab; subst hab; simp; linarith
  · rcases eq_or_lt_of_le hb with rfl | hb_pos
    · simp at hab; subst hab; simp; linarith
    · have h1 : a * h.offset < a * ⟪h.normal, x⟫_ℝ := mul_lt_mul_of_pos_left hx ha_pos
      have h2 : b * h.offset < b * ⟪h.normal, y⟫_ℝ := mul_lt_mul_of_pos_left hy hb_pos
      have h3 : a * h.offset + b * h.offset = h.offset := by
        have := congr_arg (· * h.offset) hab; simp [add_mul] at this; linarith
      linarith

/-- Open half-spaces are open subsets of $E$. -/
theorem HalfSpaceOpen (h : AffineHyperplane E) : IsOpen h.positiveHalfSpace := by
  apply isOpen_lt continuous_const
  exact continuous_const.inner continuous_id
