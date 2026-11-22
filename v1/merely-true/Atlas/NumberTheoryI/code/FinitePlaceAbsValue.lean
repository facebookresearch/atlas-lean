/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.CompleteFields
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

open NumberField IsDedekindDomain
open scoped NNReal

variable {K : Type*} [Field K] [NumberField K]

namespace FinitePlace

noncomputable def toAbsoluteValue (v : HeightOneSpectrum (𝓞 K)) : AbsoluteValue K ℝ :=
  HeightOneSpectrum.adicAbv K v

theorem toAbsoluteValue_isNontrivial (v : HeightOneSpectrum (𝓞 K)) :
    (toAbsoluteValue v).IsNontrivial := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  refine ⟨π, ?_, ?_⟩
  · intro h
    rw [h, map_zero] at hπ
    exact absurd hπ (by decide)
  · show HeightOneSpectrum.adicAbv K v π ≠ 1
    rw [HeightOneSpectrum.adicAbv_def]
    intro h
    have hne0 := HeightOneSpectrum.absNorm_ne_zero v
    have hne : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 1 :=
      ne_of_gt (HeightOneSpectrum.one_lt_absNorm_nnreal v)
    have hNN : WithZeroMulInt.toNNReal hne0 (v.valuation K π) = 1 := by exact_mod_cast h
    rw [WithZeroMulInt.toNNReal_eq_one_iff _ hne0 hne] at hNN
    rw [hNN] at hπ
    exact absurd hπ (by decide)

theorem toAbsoluteValue_pairwise_inequiv (v₁ v₂ : HeightOneSpectrum (𝓞 K)) (h : v₁ ≠ v₂) :
    ¬ (toAbsoluteValue v₁).IsEquiv (toAbsoluteValue v₂) := by
  intro heq
  have hne : v₁.asIdeal ≠ v₂.asIdeal := fun hab ↦ h (HeightOneSpectrum.ext_iff.mpr hab)
  obtain ⟨x, hx1, hx2⟩ : ∃ x : 𝓞 K, x ∈ v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra! H
    exact hne (Ideal.IsMaximal.eq_of_le v₁.isMaximal (Ideal.IsPrime.ne_top v₂.isPrime) H)
  have hlt : HeightOneSpectrum.adicAbv K v₁ (algebraMap _ K x) < 1 := by
    rw [← NumberField.FinitePlace.norm_embedding]
    exact (NumberField.FinitePlace.norm_lt_one_iff_mem K v₁ x).mpr hx1
  have heq1 : HeightOneSpectrum.adicAbv K v₂ (algebraMap _ K x) = 1 := by
    rw [← NumberField.FinitePlace.norm_embedding]
    exact (NumberField.FinitePlace.norm_eq_one_iff_notMem K v₂ x).mpr hx2
  have h1 : ¬ (1 ≤ HeightOneSpectrum.adicAbv K v₁ (algebraMap _ K x)) := not_le.mpr hlt
  have h2 : 1 ≤ HeightOneSpectrum.adicAbv K v₂ (algebraMap _ K x) := le_of_eq heq1.symm
  have h3 := (heq 1 (algebraMap _ K x)).mpr
  simp only [map_one] at h3
  exact h1 (h3 h2)

end FinitePlace
