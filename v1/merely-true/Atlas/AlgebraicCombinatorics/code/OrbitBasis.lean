/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

set_option autoImplicit false

noncomputable section

open scoped Classical

open Finset Finsupp MulAction Function Module

namespace OrbitBasis

variable (G : Type*) [Group G] (α : Type*) [Fintype α] [DecidableEq α] [MulAction G α]

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction
  Finsupp.comapDistribMulAction

def rep (O : orbitRel.Quotient G α) : α :=
  (orbitRel.Quotient.nonempty_orbit O).choose

lemma rep_mem_orbit (O : orbitRel.Quotient G α) :
    rep G α O ∈ orbitRel.Quotient.orbit O :=
  (orbitRel.Quotient.nonempty_orbit O).choose_spec

lemma mk_rep (O : orbitRel.Quotient G α) :
    (Quotient.mk'' (rep G α O) : orbitRel.Quotient G α) = O :=
  orbitRel.Quotient.mem_orbit.mp (rep_mem_orbit G α O)

def invariantSubspace : Submodule ℝ (α →₀ ℝ) where
  carrier := {v | ∀ g : G, g • v = v}
  add_mem' {a b} ha hb g := by
    have := ha g; have := hb g
    ext x; simp only [Finsupp.add_apply, Finsupp.comapSMul_apply]
    rw [← DFunLike.congr_fun (ha g) x, ← DFunLike.congr_fun (hb g) x]
    simp [Finsupp.comapSMul_apply]
  zero_mem' g := by ext x; simp

  smul_mem' r {v} hv g := by
    ext a
    change (g • (r • v)) a = (r • v) a
    rw [Finsupp.comapSMul_apply]
    have h4 := DFunLike.congr_fun (hv g) a
    rw [Finsupp.comapSMul_apply] at h4
    simp only [Finsupp.smul_apply, smul_eq_mul, h4]

variable {G α}

theorem invariant_iff_constant_on_orbits {v : α →₀ ℝ} :
    v ∈ invariantSubspace G α ↔
      ∀ a b : α, (Quotient.mk'' a : orbitRel.Quotient G α) = Quotient.mk'' b →
        v a = v b := by
  constructor
  · intro hv a b hab
    have hmem := Quotient.eq''.mp hab
    rw [orbitRel_apply] at hmem
    obtain ⟨g, hg⟩ := hmem
    have h1 := DFunLike.congr_fun (hv g) a
    rw [Finsupp.comapSMul_apply] at h1
    rw [← h1, ← hg, inv_smul_smul]
  · intro hconst g
    ext a
    rw [Finsupp.comapSMul_apply]
    exact (hconst _ _ (Quotient.eq''.mpr (orbitRel_apply.mpr ⟨g, smul_inv_smul g a⟩))).symm

def orbitSum (O : orbitRel.Quotient G α) : α →₀ ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a => a ∈ orbitRel.Quotient.orbit O),
    Finsupp.single a 1

theorem orbitSum_apply (O : orbitRel.Quotient G α) (a : α) :
    orbitSum O a = if a ∈ orbitRel.Quotient.orbit O then 1 else 0 := by
  simp only [orbitSum, Finsupp.finset_sum_apply, Finsupp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hne; exact if_neg hne
    · intro ha
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩) ha
  · apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_filter] at hb
    exact if_neg (fun heq : b = a => h (heq ▸ hb.2))

theorem orbitSum_mem_invariantSubspace (O : orbitRel.Quotient G α) :
    orbitSum O ∈ invariantSubspace G α := by
  rw [invariant_iff_constant_on_orbits]
  intro a b hab
  rw [orbitSum_apply, orbitSum_apply]
  have hiff : a ∈ orbitRel.Quotient.orbit O ↔ b ∈ orbitRel.Quotient.orbit O := by
    simp only [orbitRel.Quotient.mem_orbit]
    exact ⟨fun h => hab ▸ h, fun h => hab.symm ▸ h⟩
  by_cases ha : a ∈ orbitRel.Quotient.orbit O
  · rw [if_pos ha, if_pos (hiff.mp ha)]
  · rw [if_neg ha, if_neg (mt hiff.mpr ha)]

omit [Fintype α] [DecidableEq α] in
theorem quotient_eq_of_mem_orbit {a : α} {O : orbitRel.Quotient G α}
    (h : a ∈ orbitRel.Quotient.orbit O) :
    (Quotient.mk'' a : orbitRel.Quotient G α) = O :=
  orbitRel.Quotient.mem_orbit.mp h

omit [DecidableEq α] in

theorem sum_orbit_indicator (c : orbitRel.Quotient G α → ℝ) (a : α)
    (O₀ : orbitRel.Quotient G α)
    (ha : a ∈ orbitRel.Quotient.orbit O₀) :
    (∑ O : orbitRel.Quotient G α,
      c O * if a ∈ orbitRel.Quotient.orbit O then (1 : ℝ) else 0) = c O₀ := by
  rw [Finset.sum_eq_single O₀]
  · rw [if_pos ha, mul_one]
  · intro O' _ hO'
    have : ¬(a ∈ orbitRel.Quotient.orbit O') := by
      intro hmem
      exact hO' ((quotient_eq_of_mem_orbit hmem).symm.trans (quotient_eq_of_mem_orbit ha))
    rw [if_neg this, mul_zero]
  · intro habs; exact absurd (Finset.mem_univ _) habs

theorem orbitSum_linearIndependent :
    LinearIndependent ℝ (fun O : orbitRel.Quotient G α =>
      (⟨orbitSum O, orbitSum_mem_invariantSubspace O⟩ :
        ↥(invariantSubspace G α))) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg O
  obtain ⟨a, ha⟩ := orbitRel.Quotient.nonempty_orbit O
  have hval : (∑ O', f O' • (⟨orbitSum O', orbitSum_mem_invariantSubspace O'⟩ :
      ↥(invariantSubspace G α))).val =
    (∑ O', g O' • (⟨orbitSum O', orbitSum_mem_invariantSubspace O'⟩ :
      ↥(invariantSubspace G α))).val := congrArg Subtype.val hfg
  have heq := DFunLike.congr_fun hval a
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul, orbitSum_apply] at heq
  rw [sum_orbit_indicator f a O ha, sum_orbit_indicator g a O ha] at heq
  exact heq

theorem orbitSum_span :
    ⊤ ≤ Submodule.span ℝ (Set.range (fun O : orbitRel.Quotient G α =>
      (⟨orbitSum O, orbitSum_mem_invariantSubspace O⟩ :
        ↥(invariantSubspace G α)))) := by
  intro ⟨v, hv⟩ _
  suffices hkey : v = ∑ O : orbitRel.Quotient G α, v (rep G α O) • orbitSum O by
    have hmem : (⟨v, hv⟩ : ↥(invariantSubspace G α)) =
        ∑ O : orbitRel.Quotient G α,
          v (rep G α O) • ⟨orbitSum O, orbitSum_mem_invariantSubspace O⟩ := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
      exact hkey
    rw [hmem]
    exact Submodule.sum_mem _ (fun O _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨O, rfl⟩))
  ext a
  simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, orbitSum_apply]
  have ha : a ∈ orbitRel.Quotient.orbit
      (Quotient.mk'' a : orbitRel.Quotient G α) := by
    rw [orbitRel.Quotient.orbit_mk]; exact mem_orbit_self a
  rw [sum_orbit_indicator _ a _ ha]
  symm
  exact invariant_iff_constant_on_orbits.mp hv _ a (mk_rep G α _)

noncomputable def orbitSumBasis :
    Basis (orbitRel.Quotient G α) ℝ ↥(invariantSubspace G α) :=
  Basis.mk orbitSum_linearIndependent orbitSum_span

end OrbitBasis

end
