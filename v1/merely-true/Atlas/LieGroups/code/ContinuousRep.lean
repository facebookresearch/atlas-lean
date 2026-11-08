/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Sequences

noncomputable section

open scoped ComplexOrder

structure ContinuousRep
    (G : Type*) [Group G] [TopologicalSpace G]
    (V : Type*) [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] where
  toMonoidHom : G →* (V →L[ℂ] V)
  continuous_action : Continuous (fun p : G × V => (toMonoidHom p.1) p.2)

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]

def ofElem (π : ContinuousRep G V) (g : G) : V →L[ℂ] V := π.toMonoidHom g

structure IsInvariantSubspace (π : ContinuousRep G V)
    (W : Submodule ℂ V) : Prop where
  isClosed : IsClosed (W : Set V)
  invariant : ∀ (g : G) (v : V), v ∈ W → (π.toMonoidHom g) v ∈ W

def IsIrreducible (π : ContinuousRep G V) : Prop :=
  ∀ (W : Submodule ℂ V), π.IsInvariantSubspace W → W = ⊥ ∨ W = ⊤

def directSum
    (π₁ : ContinuousRep G V) (π₂ : ContinuousRep G W) :
    ContinuousRep G (V × W) where
  toMonoidHom :=
  { toFun := fun g => (π₁.toMonoidHom g).prodMap (π₂.toMonoidHom g)
    map_one' := by ext <;> simp
    map_mul' := fun g h => by ext <;> simp }
  continuous_action := by
    show Continuous (fun p : G × (V × W) =>
      ((π₁.toMonoidHom p.1) p.2.1, (π₂.toMonoidHom p.1) p.2.2))
    have h1 : Continuous (fun p : G × (V × W) => (π₁.toMonoidHom p.1) p.2.1) :=
      π₁.continuous_action.comp
        (by fun_prop : Continuous (fun p : G × (V × W) => (p.1, p.2.1)))
    have h2 : Continuous (fun p : G × (V × W) => (π₂.toMonoidHom p.1) p.2.2) :=
      π₂.continuous_action.comp
        (by fun_prop : Continuous (fun p : G × (V × W) => (p.1, p.2.2)))
    fun_prop

def IsUnitary {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (π : ContinuousRep G E) : Prop :=
  ∀ g : G,
    ContinuousLinearMap.adjoint (π.toMonoidHom g) * (π.toMonoidHom g) = 1 ∧
    (π.toMonoidHom g) * ContinuousLinearMap.adjoint (π.toMonoidHom g) = 1

def IsStronglyContinuous
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (π : G →* (V →L[ℂ] V)) : Prop :=
  ∀ v : V, Continuous (fun g => (π g) v)

theorem stronglyContinuous_of_continuousRep
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ρ : ContinuousRep G V) :
    IsStronglyContinuous ρ.toMonoidHom := by
  intro v
  exact ρ.continuous_action.comp (Continuous.prodMk continuous_id continuous_const)

theorem continuousRep_of_stronglyContinuous
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    [SequentialSpace (G × V)]
    (π : G →* (V →L[ℂ] V))
    (hsc : IsStronglyContinuous π) :
    Continuous (fun p : G × V => (π p.1) p.2) := by
  apply SeqContinuous.continuous
  intro u p hu
  have hg : Filter.Tendsto (fun n => (u n).1) Filter.atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hu
  have hv : Filter.Tendsto (fun n => (u n).2) Filter.atTop (nhds p.2) :=
    (continuous_snd.tendsto p).comp hu

  have hconv : Filter.Tendsto (fun n => (π (u n).1) p.2) Filter.atTop
      (nhds ((π p.1) p.2)) :=
    ((hsc p.2).tendsto p.1).comp hg

  have hptwise : ∀ w : V, ∃ C, ∀ n, ‖(π (u n).1) w‖ ≤ C := by
    intro w
    have hw := ((hsc w).tendsto p.1).comp hg
    have hb := hw.norm.isBoundedUnder_le.bddAbove_range
    rw [bddAbove_def] at hb; obtain ⟨C, hC⟩ := hb
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hptwise

  have hdiff : Filter.Tendsto (fun n => (u n).2 - p.2) Filter.atTop (nhds 0) := by
    rw [← sub_self p.2]; exact hv.sub tendsto_const_nhds

  have herr : Filter.Tendsto (fun n => (π (u n).1) ((u n).2 - p.2))
      Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop] at hdiff ⊢
    intro ε hε
    by_cases hC0 : C ≤ 0
    · obtain ⟨N, hN⟩ := hdiff ε hε
      exact ⟨N, fun n hn => by
        simp only [dist_zero_right]
        calc ‖(π (u n).1) ((u n).2 - p.2)‖
            ≤ ‖π (u n).1‖ * ‖(u n).2 - p.2‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ 0 * ‖(u n).2 - p.2‖ :=
              mul_le_mul_of_nonneg_right ((hC n).trans hC0) (norm_nonneg _)
          _ = 0 := zero_mul _
          _ < ε := hε⟩
    · push Not at hC0
      obtain ⟨N, hN⟩ := hdiff (ε / C) (div_pos hε hC0)
      exact ⟨N, fun n hn => by
        simp only [dist_zero_right] at hN ⊢
        calc ‖(π (u n).1) ((u n).2 - p.2)‖
            ≤ ‖π (u n).1‖ * ‖(u n).2 - p.2‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ C * ‖(u n).2 - p.2‖ :=
              mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)
          _ < C * (ε / C) := by
              apply mul_lt_mul_of_pos_left (hN n hn) hC0
          _ = ε := mul_div_cancel₀ ε (ne_of_gt hC0)⟩

  show Filter.Tendsto ((fun p => (π p.1) p.2) ∘ u) Filter.atTop (nhds ((π p.1) p.2))
  have : Filter.Tendsto (fun n => (π (u n).1) ((u n).2 - p.2) + (π (u n).1) p.2)
      Filter.atTop (nhds ((π p.1) p.2)) := by
    rw [show (π p.1) p.2 = 0 + (π p.1) p.2 from (zero_add _).symm]
    exact herr.add hconv
  apply Filter.Tendsto.congr (fun n => ?_) this
  simp [Function.comp, map_sub, sub_add_cancel]

theorem continuousRep_iff_stronglyContinuous
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    [SequentialSpace (G × V)]
    (π : G →* (V →L[ℂ] V)) :
    Continuous (fun p : G × V => (π p.1) p.2) ↔ IsStronglyContinuous π :=
  ⟨fun hcont => stronglyContinuous_of_continuousRep ⟨π, hcont⟩,
   fun hsc => continuousRep_of_stronglyContinuous π hsc⟩

end ContinuousRep

structure RepHom
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (π₁ : ContinuousRep G V) (π₂ : ContinuousRep G W) where
  toContinuousLinearMap : V →L[ℂ] W
  intertwines : ∀ g : G,
    toContinuousLinearMap.comp (π₁.toMonoidHom g) =
    (π₂.toMonoidHom g).comp toContinuousLinearMap

structure RepEquiv
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (π₁ : ContinuousRep G V) (π₂ : ContinuousRep G W) where
  toContinuousLinearEquiv : V ≃L[ℂ] W
  intertwines : ∀ g : G,
    (toContinuousLinearEquiv : V →L[ℂ] W).comp (π₁.toMonoidHom g) =
    (π₂.toMonoidHom g).comp (toContinuousLinearEquiv : V →L[ℂ] W)

def RepEquiv.toRepHom
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    {π₁ : ContinuousRep G V} {π₂ : ContinuousRep G W}
    (e : RepEquiv π₁ π₂) : RepHom π₁ π₂ where
  toContinuousLinearMap := e.toContinuousLinearEquiv
  intertwines := e.intertwines

end
