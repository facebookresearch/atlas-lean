/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory Set intervalIntegral Filter

noncomputable section

namespace Chapter3

/-- Haar mother wavelet on `[0,1]`: equals `1` on `[0, 1/2)`, `-1` on
`[1/2, 1]`, and zero elsewhere. -/
def haarMother (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x < 1 / 2 then 1
  else if 1 / 2 ≤ x ∧ x ≤ 1 then -1
  else 0

/-- Haar wavelet at scale `j` and translation `k`:
`ψ_{j,k}(x) = 2^{j/2} ψ(2^j x - k)` where `ψ` is the Haar mother wavelet. -/
def haarWavelet (j k : ℤ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ ((j : ℝ) / 2) * haarMother ((2 : ℝ) ^ (j : ℤ) * x - ↑k)

/-- Wavelet coefficient of `g` at scale `j` and translation `k`:
`∫₀¹ g(x) ψ_{j,k}(x) dx`. -/
def waveletCoeff (g : ℝ → ℝ) (j k : ℤ) : ℝ :=
  ∫ x in (0 : ℝ)..1, g x * haarWavelet j k x

/-- The Haar mother wavelet is strongly measurable. -/
lemma haarMother_stronglyMeasurable : StronglyMeasurable haarMother := by
  unfold haarMother
  exact StronglyMeasurable.ite (measurableSet_Ici.inter measurableSet_Iio)
    stronglyMeasurable_const (StronglyMeasurable.ite
      (measurableSet_Ici.inter measurableSet_Iic)
      stronglyMeasurable_const stronglyMeasurable_const)

/-- The Haar mother wavelet is interval-integrable on every `[a,b]`. -/
lemma haarMother_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable haarMother volume a b := by
  apply (intervalIntegral.intervalIntegrable_const (c := (1 : ℝ))).mono_fun
  · exact haarMother_stronglyMeasurable.aestronglyMeasurable.restrict
  · apply ae_of_all; intro x; simp only [haarMother]; split_ifs <;> simp

/-- Almost everywhere on `(0, 1/2]`, the Haar mother wavelet equals `1`. -/
lemma haar_ae_first :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ uIoc 0 (1/2 : ℝ) → haarMother x = 1 := by
  rw [eventually_iff, mem_ae_iff]
  apply measure_mono_null
  show {x : ℝ | x ∈ uIoc 0 (1/2) → haarMother x = 1}ᶜ ⊆ {1/2}
  · intro x hx
    simp only [mem_compl_iff, mem_setOf_eq] at hx; push_neg at hx
    obtain ⟨hxm, hne⟩ := hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1/2), mem_Ioc] at hxm
    simp only [mem_singleton_iff]; by_contra h
    exact hne (by unfold haarMother; rw [if_pos ⟨le_of_lt hxm.1, lt_of_le_of_ne hxm.2 h⟩])
  · simp

end Chapter3
