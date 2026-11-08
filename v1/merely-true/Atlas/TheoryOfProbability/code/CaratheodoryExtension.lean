/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.MeasureTheory.Measure.MeasureSpace

open scoped ENNReal

noncomputable section

open Set MeasureTheory MeasureTheory.Measure MeasurableSpace

/-- Every set algebra is a set semiring: combine the set-ring structure (empty set,
closure under union, closure under difference) and view the resulting ring as a
semiring. -/
def isSetSemiring_of_isSetAlgebra {α : Type*} {𝒜 : Set (Set α)} (h : IsSetAlgebra 𝒜) :
    IsSetSemiring 𝒜 :=
  (IsSetRing.mk h.empty_mem (fun {_} {_} hs ht => h.union_mem hs ht)
    (fun {_} {_} hs ht => h.diff_mem hs ht)).isSetSemiring

/-- A set algebra `𝒜` is automatically a `π`-system: it is closed under finite
intersections. -/
lemma isSetAlgebra_isPiSystem {α : Type*} {𝒜 : Set (Set α)} (h : IsSetAlgebra 𝒜) :
    IsPiSystem 𝒜 := fun _s hs _t ht _ => h.inter_mem hs ht

/-- Existence part of the Carathéodory extension theorem: any `σ`-subadditive
`AddContent` `μ₀` on a set algebra `𝒜` extends to a measure on the generated
`σ`-algebra `σ(𝒜)`, agreeing with `μ₀` on `𝒜`. -/
lemma exists_measure_extension
    {α : Type*}
    (𝒜 : Set (Set α))
    (h𝒜 : IsSetAlgebra 𝒜)
    (μ₀ : AddContent ℝ≥0∞ 𝒜)
    (hμ₀_sigma : μ₀.IsSigmaSubadditive) :
    ∃ μ : @Measure α (generateFrom 𝒜), ∀ s ∈ 𝒜, μ s = μ₀ s := by
  letI : MeasurableSpace α := generateFrom 𝒜
  have h_semi : IsSetSemiring 𝒜 := isSetSemiring_of_isSetAlgebra h𝒜
  exact ⟨μ₀.measure h_semi le_rfl hμ₀_sigma, fun s hs =>
    μ₀.measure_eq h_semi rfl hμ₀_sigma hs⟩

/-- **Carathéodory extension theorem.** If `μ₀` is a `σ`-finite (witnessed by a
cover `B : ℕ → 𝒜` with `μ₀ (B i) < ∞`) `σ`-subadditive additive content on a set
algebra `𝒜`, then there exists a *unique* measure on `σ(𝒜)` extending `μ₀`. -/
theorem caratheodory_extension_theorem
    {α : Type*}
    (𝒜 : Set (Set α))
    (h𝒜 : IsSetAlgebra 𝒜)
    (μ₀ : AddContent ℝ≥0∞ 𝒜)
    (hμ₀_sigma : μ₀.IsSigmaSubadditive)
    (B : ℕ → Set α)
    (hB_mem : ∀ i, B i ∈ 𝒜)
    (hB_cover : ⋃ i, B i = univ)
    (hB_fin : ∀ i, μ₀ (B i) ≠ ⊤) :
    ∃! μ : @Measure α (generateFrom 𝒜), ∀ s ∈ 𝒜, μ s = μ₀ s := by

  obtain ⟨μ, hμ⟩ := exists_measure_extension 𝒜 h𝒜 μ₀ hμ₀_sigma

  refine ⟨μ, hμ, fun ν hν => ?_⟩


  exact (ext_of_generateFrom_of_iUnion 𝒜 B rfl (isSetAlgebra_isPiSystem h𝒜) hB_cover hB_mem
    (fun i => by rw [hμ (B i) (hB_mem i)]; exact hB_fin i)
    (fun s hs => by rw [hμ s hs, hν s hs])).symm
