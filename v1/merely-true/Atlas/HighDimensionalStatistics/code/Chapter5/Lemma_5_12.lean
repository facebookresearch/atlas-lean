/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory

open Finset Real

noncomputable section

namespace VarshamovGilbert

/-- Hamming distance between two binary vectors `ω₁, ω₂ ∈ {0,1}^d`: the number
of coordinates on which they disagree. -/
def hammingDist {d : ℕ} (ω₁ ω₂ : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω₁ i ≠ ω₂ i).card

/-- Varshamov–Gilbert lemma (Lemma 5.12): for `γ ∈ (0, 1/2)` and `d ≥ 1`,
there exist `M ≥ exp(γ²d/2)` binary vectors `ω₁, …, ω_M ∈ {0, 1}^d` with
pairwise Hamming distance at least `(1/2 - γ) d`. -/
theorem varshamov_gilbert (d : ℕ) (hd : 0 < d) (γ : ℝ) (hγ_pos : 0 < γ) (hγ_lt : γ < 1/2) :
    ∃ (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)),
    (M : ℝ) ≥ Real.exp (γ ^ 2 * d / 2) ∧
    ∀ j k : Fin M, j ≠ k →
      (hammingDist (ω j) (ω k) : ℝ) ≥ (1/2 - γ) * d := by
  obtain ⟨M, hM, ω, hbound, hsep⟩ := InfoTheory.varshamov_gilbert d hd γ hγ_pos hγ_lt
  exact ⟨M, hM, ω, hbound, fun j k hjk => by
    have := hsep j k hjk
    simp only [InfoTheory.hammingDist, hammingDist] at this ⊢
    exact this⟩

end VarshamovGilbert

end
