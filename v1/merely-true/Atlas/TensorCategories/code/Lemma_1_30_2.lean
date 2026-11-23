/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Finiteness.Defs

set_option maxHeartbeats 400000

universe u v

variable (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V]

/-- An element of `GL(V)` is unipotent if `g - id` is a nilpotent linear endomorphism. -/
def IsUnipotentElem (g : LinearMap.GeneralLinearGroup k V) : Prop :=
  IsNilpotent (g.val - LinearMap.id)

/-- A subgroup `N ≤ GL(V)` is unipotent if every element is unipotent. -/
def IsUnipotentSubgroup (N : Subgroup (LinearMap.GeneralLinearGroup k V)) : Prop :=
  ∀ g ∈ N, IsUnipotentElem k V g

/-- A subgroup `G ≤ GL(V)` is reductive (in the sense of Definition 1.30.1) if its only
unipotent normal subgroup is trivial. -/
def IsReductiveSubgroup (G : Subgroup (LinearMap.GeneralLinearGroup k V)) : Prop :=
  ∀ N : Subgroup (LinearMap.GeneralLinearGroup k V),
    N ≤ G → N.Normal → IsUnipotentSubgroup k V N → N = ⊥

/-- A submodule `W ≤ V` is invariant under `G ≤ GL(V)` if every element of `G` maps `W` to
itself. -/
def IsInvariantSubmodule
    (G : Subgroup (LinearMap.GeneralLinearGroup k V))
    (W : Submodule k V) : Prop :=
  ∀ g ∈ G, ∀ w ∈ W, (g.val : V →ₗ[k] V) w ∈ W

/-- The defining representation of `G ≤ GL(V)` on `V` is completely reducible if every
`G`-invariant submodule admits a `G`-invariant complement. -/
def IsCompletelyReducibleRep
    (G : Subgroup (LinearMap.GeneralLinearGroup k V)) : Prop :=
  ∀ W : Submodule k V, IsInvariantSubmodule k V G W →
    ∃ W' : Submodule k V, IsInvariantSubmodule k V G W' ∧
      W ⊔ W' = ⊤ ∧ W ⊓ W' = ⊥

/-- The submodule `V^N` of vectors fixed by every element of `N ≤ GL(V)`. -/
def invariantsSubmodule (N : Subgroup (LinearMap.GeneralLinearGroup k V)) : Submodule k V where
  carrier := { w : V | ∀ g ∈ N, (g.val : V →ₗ[k] V) w = w }
  add_mem' := by intro a b ha hb g hg; simp [map_add, ha g hg, hb g hg]
  zero_mem' := by intro g hg; simp [map_zero]
  smul_mem' := by intro c x hx g hg; simp [hx g hg]


/-- Membership in the invariants submodule unfolds to the pointwise fixedness condition. -/
lemma mem_invariantsSubmodule (N : Subgroup (LinearMap.GeneralLinearGroup k V)) (w : V) :
    w ∈ invariantsSubmodule k V N ↔ ∀ g ∈ N, (g.val : V →ₗ[k] V) w = w := by
  simp [invariantsSubmodule, Submodule.mem_mk, Set.mem_setOf_eq]

/-- For a normal subgroup `N ⊴ G`, the submodule of `N`-invariants is itself `G`-invariant. -/
lemma invariants_G_invariant
    (G N : Subgroup (LinearMap.GeneralLinearGroup k V))
    (_hNG : N ≤ G)
    (hNormal : N.Normal) :
    IsInvariantSubmodule k V G (invariantsSubmodule k V N) := by
  intro g hg w hw
  simp only [invariantsSubmodule, Submodule.mem_mk] at hw ⊢
  intro n hn
  have h_conj : g⁻¹ * n * g ∈ N := hNormal.conj_mem n hn g⁻¹
  have key : (g⁻¹ * n * g).val w = w := hw _ h_conj
  have : (g⁻¹ * n * g).val w = (g⁻¹).val (n.val (g.val w)) := rfl
  rw [this] at key
  have := congr_arg g.val key
  change g.toLinearEquiv ((g.toLinearEquiv).symm (n.val (g.val w))) = g.val w at this
  rw [g.toLinearEquiv.apply_symm_apply] at this
  exact this

/-- A subgroup of an invariance group still leaves the subspace invariant. -/
lemma invariant_of_le
    (G N : Subgroup (LinearMap.GeneralLinearGroup k V))
    (hNG : N ≤ G)
    (W : Submodule k V)
    (hW : IsInvariantSubmodule k V G W) :
    IsInvariantSubmodule k V N W :=
  fun g hg w hw => hW g (hNG hg) w hw

/-- If every vector of `V` is `N`-invariant, then `N` is trivial. -/
lemma trivial_of_invariants_eq_top
    (N : Subgroup (LinearMap.GeneralLinearGroup k V))
    (h : invariantsSubmodule k V N = ⊤) :
    N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  ext v
  have : v ∈ invariantsSubmodule k V N := by rw [h]; trivial
  rw [mem_invariantsSubmodule] at this
  have := this g hg
  simp at this
  exact this



