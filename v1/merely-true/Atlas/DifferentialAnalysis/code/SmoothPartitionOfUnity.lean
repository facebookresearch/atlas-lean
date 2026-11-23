/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open Set Filter Topology Function Finset

open scoped Manifold ContDiff

namespace SmoothPartitionOfUnity

/-- Proposition 8.7 of Melrose: existence of a finite smooth partition of unity on a compact
set `K` in a finite-dimensional Euclidean space, subordinate to a given open cover `{U a}`.
The output gives finitely many `C^∞` cutoffs `φ_i` valued in `[0,1]` with `tsupport (φ i)`
contained in some `U (a i)`, summing to `1` on an open neighbourhood of `K`. -/
theorem exists_smooth_finitePartition_of_isCompact
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {A : Type*} {U : A → Set E} {K : Set E}
    (hU : ∀ a, IsOpen (U a))
    (hK : IsCompact K)
    (hKU : K ⊆ ⋃ a, U a) :
    ∃ (N : ℕ) (φ : Fin N → E → ℝ) (a : Fin N → A),
      (∀ i, ContDiff ℝ ∞ (φ i)) ∧
      (∀ i x, 0 ≤ φ i x) ∧
      (∀ i x, φ i x ≤ 1) ∧
      (∀ i, tsupport (φ i) ⊆ U (a i)) ∧
      (∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, ∑ i : Fin N, φ i x = 1) := by

  have hUopen : IsOpen (⋃ a, U a) := isOpen_iUnion hU
  obtain ⟨L, hL_compact, hKL, hLU⟩ := exists_compact_between hK hUopen hKU

  obtain ⟨ρ, hρ_sub⟩ := _root_.SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, E) hL_compact.isClosed U hU hLU

  have hlf := ρ.locallyFinite
  have hfinL : {a : A | (Function.support (⇑(ρ a)) ∩ L).Nonempty}.Finite :=
    hlf.finite_nonempty_inter_compact hL_compact
  let S := hfinL.toFinset
  let N := S.card
  let e := S.equivFin

  refine ⟨N, fun i => ρ (e.symm i).val, fun i => (e.symm i).val,
    ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i; exact (ρ (e.symm i).val).contMDiff.contDiff
  ·
    intro i x; exact ρ.nonneg _ x
  ·
    intro i x; exact ρ.le_one _ x
  ·
    intro i; exact hρ_sub (e.symm i).val
  ·

    refine ⟨interior L, isOpen_interior, hKL, ?_⟩
    intro x hx
    have hxL : x ∈ L := interior_subset hx

    have hsupp_sub : (Function.support fun a => ρ a x) ⊆ ↑S := by
      intro a ha
      exact hfinL.mem_toFinset.mpr
        ⟨x, Function.mem_support.mpr (Function.mem_support.mp ha), hxL⟩
    have hfinsum_eq : ∑ᶠ a, ρ a x = ∑ a ∈ S, ρ a x :=
      finsum_eq_sum_of_support_subset _ hsupp_sub
    rw [ρ.sum_eq_one hxL] at hfinsum_eq

    have hsum_eq : ∑ i : Fin N, (ρ (e.symm i).val) x = ∑ a ∈ S, ρ a x := by
      rw [← S.sum_coe_sort (fun a => (ρ a) x)]
      exact Fintype.sum_equiv e.symm _ _ (fun i => rfl)
    linarith

end SmoothPartitionOfUnity

section ContinuousPartitionOfUnity

variable {X : Type*} [TopologicalSpace X]

/-- Continuous partition of unity variant of Proposition 8.7: on a locally compact Hausdorff
space `X`, any compact `K` covered by finitely many open sets `U i` admits a continuous
partition of unity subordinate to the cover, with each `f i` having compact support. -/
theorem exists_continuous_partition_of_isCompact [LocallyCompactSpace X] [T2Space X]
    {ι : Type*} [Fintype ι] {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ ⋃ i, U i) :
    ∃ f : ι → C(X, ℝ), (∀ i x, 0 ≤ f i x) ∧ (∀ i x, f i x ≤ 1) ∧
      (∀ i, HasCompactSupport (f i)) ∧ (∀ i, tsupport (f i) ⊆ U i) ∧
      (∃ V, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, ∑ i, f i x = 1) := by

  have hUopen : IsOpen (⋃ i, U i) := isOpen_iUnion hU
  obtain ⟨L, hL_compact, hKL, hLU⟩ := exists_compact_between hK hUopen hKU

  obtain ⟨f, hfsub, hfcp⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space
    hL_compact U hU (locallyFinite_of_finite U) hLU

  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x; exact f.nonneg i x
  · intro i x; exact PartitionOfUnity.le_one f i x
  · intro i; exact hfcp i
  · intro i; exact hfsub i
  ·
    refine ⟨interior L, isOpen_interior, hKL, ?_⟩
    intro x hx
    have hxL : x ∈ L := interior_subset hx
    have h := f.sum_eq_one' x hxL
    rw [finsum_eq_sum_of_fintype] at h
    exact h

end ContinuousPartitionOfUnity

end
