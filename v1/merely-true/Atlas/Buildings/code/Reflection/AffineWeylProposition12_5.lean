/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv

set_option maxHeartbeats 3200000

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Proposition 12.5 (i): the affine hyperplane arrangement $\{H_{α,k}\}$ associated to a
crystallographic root system is locally finite. -/
theorem affineWeylGroup_locallyFinite (d : AffineWeylGroupFullData E) :
    d.affineArr.IsLocallyFinite :=
  d.proposition_locallyFinite

/-- Proposition 12.5 (ii): the affine Weyl group has the semidirect-product structure
$W_a = W ⋉ Λ(\check Φ)$ — every affine reflection is a linear reflection plus a coroot
translation, $W$ stabilizes the coroot lattice, and the linear-part kernel is trivial. -/
theorem affineWeylGroup_semidirectProduct (d : AffineWeylGroupFullData E) :

    (∀ α ∈ d.roots, ∀ k : ℤ, ∀ v : E,
      ∃ (t : E),
        t ∈ d.corootLattice ∧
        d.affineReflFun α k v = d.linearReflFun α v + t) ∧

    (∀ w ∈ d.weylGroup, ∀ v ∈ d.corootLattice,
      (w : E ≃ₗᵢ[ℝ] E) v ∈ d.corootLattice) ∧

    (∀ (w : E ≃ₗᵢ[ℝ] E) (t : E),
      (∀ v : E, w v = v + t) → t = 0 ∧ w = 1) :=
  d.proposition_semidirectProduct

/-- Proposition 12.5 (iii): the affine arrangement is stable under coroot translations and
under the linear Weyl group. -/
theorem affineWeylGroup_stable (d : AffineWeylGroupFullData E) :

    (∀ v ∈ d.corootLattice, ∀ η ∈ d.affineArr.hyperplanes,
      ∃ η' ∈ d.affineArr.hyperplanes,
        η'.normal = η.normal ∧
        ∀ x : E, x ∈ η'.carrier ↔ (x - v) ∈ η.carrier) ∧

    (∀ w ∈ d.weylGroup, ∀ η ∈ d.affineArr.hyperplanes,
      ∃ η' ∈ d.affineArr.hyperplanes,
        η'.normal = (w : E ≃ₗᵢ[ℝ] E) η.normal ∧
        η'.offset = η.offset) :=
  d.proposition_stable

/-- Translation by $\check α$ equals the composition $s_{α,1} \circ s_{α,0}$ of two
affine reflections. -/
theorem coroot_translation_eq_composition (d : AffineWeylGroupFullData E)
    (α : E) (hα : α ∈ d.roots) :
    ∀ v : E, v + d.coroot α = d.affineReflFun α 1 (d.affineReflFun α 0 v) :=
  d.coroot_translation_is_product_of_reflections α hα
