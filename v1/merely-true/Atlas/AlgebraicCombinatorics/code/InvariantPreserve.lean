/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.OrbitBasis
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.LinearAlgebra.Finsupp.LSum

set_option autoImplicit false

noncomputable section

open scoped Classical Pointwise

open Finset Finsupp MulAction Function

namespace InvariantPreserve

variable (n : ℕ)

def upperCovers (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun T => S ⊂ T ∧ T.card = S.card + 1

def raisingOnBasis (S : Finset (Fin n)) : Finset (Fin n) →₀ ℝ :=
  (upperCovers n S).sum fun T => Finsupp.single T 1

def raisingOp : (Finset (Fin n) →₀ ℝ) →ₗ[ℝ] (Finset (Fin n) →₀ ℝ) :=
  Finsupp.lsum ℝ fun S => LinearMap.toSpanSingleton ℝ _ (raisingOnBasis n S)

@[simp]
theorem raisingOp_single (S : Finset (Fin n)) (r : ℝ) :
    raisingOp n (Finsupp.single S r) = r • raisingOnBasis n S := by
  simp only [raisingOp, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

variable (G : Type*) [Group G] [MulAction G (Fin n)]

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction
  Finsupp.comapDistribMulAction

@[simp]
lemma comapSMul_zero (g : G) :
    (g • (0 : Finset (Fin n) →₀ ℝ)) = 0 :=
  Finsupp.mapDomain_zero

@[simp]
lemma comapSMul_eq_mapDomain (g : G) (v : Finset (Fin n) →₀ ℝ) :
    g • v = Finsupp.mapDomain (g • ·) v := rfl

@[simp]
lemma comapSMul_add (g : G) (v w : Finset (Fin n) →₀ ℝ) :
    g • (v + w) = g • v + g • w := by
  simp only [comapSMul_eq_mapDomain, Finsupp.mapDomain_add]

lemma smul_ssubset (g : G) (S T : Finset (Fin n)) (h : S ⊂ T) :
    g • S ⊂ g • T :=
  (Finset.image_ssubset_image (MulAction.injective g)).mpr h

lemma smul_upperCovers (g : G) (S : Finset (Fin n)) :
    (upperCovers n S).image (g • ·) = upperCovers n (g • S) := by
  ext T
  simp only [upperCovers, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨T', ⟨hss, hcard⟩, rfl⟩
    exact ⟨smul_ssubset n G g S T' hss,
           by rw [Finset.card_smul_finset, hcard, Finset.card_smul_finset]⟩
  · intro ⟨hss, hcard⟩
    refine ⟨g⁻¹ • T, ⟨?_, ?_⟩, by rw [smul_inv_smul]⟩
    · rw [← inv_smul_smul g S]
      exact smul_ssubset n G g⁻¹ (g • S) T hss
    · rw [Finset.card_smul_finset, hcard, Finset.card_smul_finset]

theorem smul_raisingOnBasis (g : G) (S : Finset (Fin n)) :
    Finsupp.mapDomain (g • ·) (raisingOnBasis n S) = raisingOnBasis n (g • S) := by
  simp only [raisingOnBasis, Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single]
  rw [← smul_upperCovers n G g S]
  rw [Finset.sum_image]
  intro T₁ _ T₂ _ h
  exact MulAction.injective g h

theorem raisingOp_comm_smul (g : G) (v : Finset (Fin n) →₀ ℝ) :
    g • raisingOp n v = raisingOp n (g • v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero, comapSMul_zero]
  | add f₁ f₂ hf₁ hf₂ =>
    simp only [map_add, comapSMul_add, hf₁, hf₂]
  | single S r =>
    simp only [raisingOp_single, comapSMul_eq_mapDomain, Finsupp.mapDomain_smul,
               Finsupp.mapDomain_single, smul_raisingOnBasis]

theorem linearMap_preserves_invariant
    (f : (Finset (Fin n) →₀ ℝ) →ₗ[ℝ] (Finset (Fin n) →₀ ℝ))
    (hcomm : ∀ g : G, ∀ v : Finset (Fin n) →₀ ℝ, g • f v = f (g • v))
    {v : Finset (Fin n) →₀ ℝ}
    (hv : v ∈ OrbitBasis.invariantSubspace G (Finset (Fin n))) :
    f v ∈ OrbitBasis.invariantSubspace G (Finset (Fin n)) := by
  intro g
  rw [hcomm g v]
  congr 1
  exact hv g

theorem raisingOp_mem_invariantSubspace
    {v : Finset (Fin n) →₀ ℝ}
    (hv : v ∈ OrbitBasis.invariantSubspace G (Finset (Fin n))) :
    raisingOp n v ∈ OrbitBasis.invariantSubspace G (Finset (Fin n)) :=
  linearMap_preserves_invariant n G (raisingOp n) (raisingOp_comm_smul n G) hv

lemma raisingOnBasis_support_subset (S : Finset (Fin n)) :
    (raisingOnBasis n S).support ⊆ upperCovers n S := by
  intro T hT
  have := Finsupp.support_finset_sum (s := upperCovers n S)
    (f := fun T => Finsupp.single T (1 : ℝ)) hT
  rw [Finset.mem_biUnion] at this
  obtain ⟨T', hT'mem, hT'sup⟩ := this
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hT'sup
  exact hT'sup ▸ hT'mem

lemma card_of_mem_upperCovers {S T : Finset (Fin n)} (hT : T ∈ upperCovers n S) :
    T.card = S.card + 1 := by
  simp only [upperCovers, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  exact hT.2

theorem raisingOp_support_card (i : ℕ) (v : Finset (Fin n) →₀ ℝ)
    (hv : ∀ x ∈ v.support, x.card = i) :
    ∀ y ∈ (raisingOp n v).support, y.card = i + 1 := by
  intro y hy
  have hrw : raisingOp n v = v.sum (fun S r => r • raisingOnBasis n S) := by
    simp only [raisingOp, Finsupp.lsum_apply]
    congr 1
  rw [hrw] at hy
  have hsup := Finsupp.support_sum hy
  rw [Finset.mem_biUnion] at hsup
  obtain ⟨S, hSmem, hySsup⟩ := hsup
  have hySrob : y ∈ (raisingOnBasis n S).support := Finsupp.support_smul hySsup
  have hT_in_uc := raisingOnBasis_support_subset n S hySrob
  have := card_of_mem_upperCovers n hT_in_uc
  rw [hv S hSmem] at this
  exact this

def supportedAtLevel (i : ℕ) (v : Finset (Fin n) →₀ ℝ) : Prop :=
  ∀ S ∈ v.support, S.card = i

theorem raisingOp_supportedAtLevel {i : ℕ} {v : Finset (Fin n) →₀ ℝ}
    (hv : supportedAtLevel n i v) :
    supportedAtLevel n (i + 1) (raisingOp n v) :=
  raisingOp_support_card n i v hv

theorem raisingOp_mem_invariantSubspace_graded
    {v : Finset (Fin n) →₀ ℝ} {i : ℕ}
    (hv_inv : v ∈ OrbitBasis.invariantSubspace G (Finset (Fin n)))
    (hv_level : supportedAtLevel n i v) :
    raisingOp n v ∈ OrbitBasis.invariantSubspace G (Finset (Fin n)) ∧
    supportedAtLevel n (i + 1) (raisingOp n v) :=
  ⟨raisingOp_mem_invariantSubspace n G hv_inv, raisingOp_supportedAtLevel n hv_level⟩

end InvariantPreserve

end
