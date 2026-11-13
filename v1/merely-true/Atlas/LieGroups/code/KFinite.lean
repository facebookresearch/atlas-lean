/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ContinuousRep
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

def IsKFinite (π : ContinuousRep G V) (K : Subgroup G) (v : V) : Prop :=
  FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) : Submodule ℂ V)

lemma isKFinite_zero (π : ContinuousRep G V) (K : Subgroup G) :
    IsKFinite π K (0 : V) := by
  unfold IsKFinite
  have hrng : Set.range (fun k : K => (π.toMonoidHom k) (0 : V)) = {0} := by
    ext x; simp
  rw [hrng, Submodule.span_singleton_eq_bot.mpr rfl]
  exact Module.Finite.bot ℂ V

lemma isKFinite_add (π : ContinuousRep G V) (K : Subgroup G) (v w : V)
    (hv : IsKFinite π K v) (hw : IsKFinite π K w) :
    IsKFinite π K (v + w) := by
  unfold IsKFinite at *
  set Sv := Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v))
  set Sw := Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) w))
  have hsub : Submodule.span ℂ
      (Set.range (fun k : K => (π.toMonoidHom k) (v + w))) ≤ Sv ⊔ Sw := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    simp only [map_add]
    exact Submodule.add_mem_sup
      (Submodule.subset_span ⟨k, rfl⟩)
      (Submodule.subset_span ⟨k, rfl⟩)
  have : FiniteDimensional ℂ ↥(Sv ⊔ Sw) := Submodule.finite_sup Sv Sw
  exact Module.Finite.of_injective
    (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)

lemma isKFinite_smul (π : ContinuousRep G V) (K : Subgroup G)
    (c : ℂ) (v : V) (hv : IsKFinite π K v) :
    IsKFinite π K (c • v) := by
  unfold IsKFinite at *
  have hsub : Submodule.span ℂ
      (Set.range (fun k : K => (π.toMonoidHom k) (c • v))) ≤
      Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    simp only [map_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, rfl⟩)
  exact Module.Finite.of_injective
    (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)

def kFiniteSubspace (π : ContinuousRep G V) (K : Subgroup G) :
    Submodule ℂ V where
  carrier := {v : V | IsKFinite π K v}
  zero_mem' := isKFinite_zero π K
  add_mem' := fun {a b} ha hb => isKFinite_add π K a b ha hb
  smul_mem' := fun c {v} hv => isKFinite_smul π K c v hv

lemma mem_kFiniteSubspace (π : ContinuousRep G V) (K : Subgroup G)
    (v : V) : v ∈ kFiniteSubspace π K ↔ IsKFinite π K v :=
  Iff.rfl

def restrictSubgroup [IsTopologicalGroup G]
    (π : ContinuousRep G V) (K : Subgroup G) :
    ContinuousRep K V where
  toMonoidHom := π.toMonoidHom.comp K.subtype
  continuous_action :=
    π.continuous_action.comp
      (Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd)

def subrepresentation
    (π : ContinuousRep G V)
    (W : Submodule ℂ V) (hW : π.IsInvariantSubspace W) :
    ContinuousRep G W where
  toMonoidHom :=
  { toFun := fun g =>
    { toLinearMap :=
      { toFun := fun ⟨v, hv⟩ =>
          ⟨(π.toMonoidHom g) v, hW.invariant g v hv⟩
        map_add' := fun ⟨v₁, _⟩ ⟨v₂, _⟩ => by ext; simp [map_add]
        map_smul' := fun c ⟨v, _⟩ => by ext; simp [map_smul] }
      cont := by
        apply Continuous.subtype_mk
        exact (π.toMonoidHom g).continuous.comp continuous_subtype_val }
    map_one' := by ext ⟨v, _⟩; simp
    map_mul' := fun g h => by ext ⟨v, _⟩; simp }
  continuous_action := by
    apply Continuous.subtype_mk
    show Continuous (fun p : G × W => (π.toMonoidHom p.1) (p.2 : V))
    exact π.continuous_action.comp
      (Continuous.prodMk continuous_fst
        (continuous_subtype_val.comp continuous_snd))

def IsotypicComponent [IsTopologicalGroup G]
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (π : ContinuousRep G V) (K : Subgroup G)
    (σ : ContinuousRep K Wσ) :
    Submodule ℂ V :=
  sSup { W : Submodule ℂ V |
    ∃ (hW : (π.restrictSubgroup K).IsInvariantSubspace W),
      ((π.restrictSubgroup K).subrepresentation W hW).IsIrreducible ∧
      Nonempty (RepEquiv
        ((π.restrictSubgroup K).subrepresentation W hW) σ) }

end ContinuousRep

end
