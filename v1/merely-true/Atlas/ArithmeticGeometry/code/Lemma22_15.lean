/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Lemma22_15

variable {Place : Type*} [DecidableEq Place]

/-- Increment a divisor $D$ by one at the place $P$, leaving all other places
unchanged. -/
def addPlace (D : Place → ℤ) (P : Place) : Place → ℤ :=
  Function.update D P (D P + 1)

/-- Value of `addPlace D P` at `P` itself: it equals $D(P) + 1$. -/
@[simp]
theorem addPlace_self (D : Place → ℤ) (P : Place) :
    addPlace D P P = D P + 1 := by
  simp [addPlace]

/-- Value of `addPlace D P` at $Q \neq P$: it is unchanged, equal to $D(Q)$. -/
theorem addPlace_ne (D : Place → ℤ) (P Q : Place) (h : Q ≠ P) :
    addPlace D P Q = D Q := by
  simp [addPlace, Function.update_of_ne h]

/-- The increment-at-`P` operation only enlarges a divisor pointwise:
$D \le \mathrm{addPlace}\,D\,P$. -/
theorem le_addPlace (D : Place → ℤ) (P : Place) :
    D ≤ addPlace D P := by
  intro Q
  by_cases h : Q = P
  · subst h; simp [addPlace]
  · exact le_of_eq (addPlace_ne D P Q h).symm

variable {Ω : Type*} [Zero Ω]

/-- Abstract statement that the divisor $D$ is maximal for the relation
`omegaD ω · `: $\omega$ is associated to $D$ and every other associated divisor
$D'$ satisfies $D' \le D$. Used to formulate the unique divisor of a Weil
differential (Lemma 22.15). -/
def IsMaximalDivisorFor (omegaD : Ω → (Place → ℤ) → Prop) (ω : Ω) (D : Place → ℤ) : Prop :=
  omegaD ω D ∧ ∀ D' : Place → ℤ, omegaD ω D' → D' ≤ D

/-- Existence half of Lemma 22.15. Under the "increment" closure hypothesis
`adele_decomp` and finiteness of associated divisors, every nonzero $\omega$
admits a maximal divisor $D$ with `omegaD ω D` and $D' \le D$ for all
associated $D'$. -/
theorem exists_maximal_divisor
    (omegaD : Ω → (Place → ℤ) → Prop)
    (adele_decomp : ∀ (ω : Ω) (D₁ D₂ : Place → ℤ) (P : Place),
      omegaD ω D₁ → omegaD ω D₂ → D₁ P < D₂ P →
      omegaD ω (addPlace D₁ P))
    (ω : Ω) (_hω : ω ≠ 0)
    (hex : ∃ D, omegaD ω D)
    (hfin : Set.Finite {D | omegaD ω D}) :
    ∃ D, IsMaximalDivisorFor omegaD ω D := by

  obtain ⟨D₀, hD₀⟩ := hex
  have hne : ({D | omegaD ω D} : Set (Place → ℤ)).Nonempty := ⟨D₀, hD₀⟩

  obtain ⟨m, hm⟩ := hfin.exists_maximal hne

  refine ⟨m, hm.prop, fun D' hD' => ?_⟩

  by_contra h_not_le
  simp only [Pi.le_def, not_forall] at h_not_le
  obtain ⟨P, hP⟩ := h_not_le
  push_neg at hP


  have h_in : omegaD ω (addPlace m P) := adele_decomp ω m D' P hm.prop hD' hP


  have h_le : addPlace m P ≤ m := hm.le_of_ge h_in (le_addPlace m P)
  exact absurd (h_le P) (by simp)

/-- Uniqueness half of Lemma 22.15. Any two maximal divisors for the same
$\omega$ coincide. -/
theorem unique_maximal_divisor
    (omegaD : Ω → (Place → ℤ) → Prop)
    (ω : Ω)
    {D₁ D₂ : Place → ℤ}
    (h₁ : IsMaximalDivisorFor omegaD ω D₁)
    (h₂ : IsMaximalDivisorFor omegaD ω D₂) :
    D₁ = D₂ :=
  le_antisymm (h₂.2 D₁ h₁.1) (h₁.2 D₂ h₂.1)

/-- Lemma 22.15 (unique maximal divisor $D_\omega$ of a Weil differential).
Combining existence and uniqueness: every nonzero $\omega$ has a unique
divisor $D$ with `IsMaximalDivisorFor omegaD ω D`. -/
theorem exists_unique_maximal_divisor
    (omegaD : Ω → (Place → ℤ) → Prop)
    (adele_decomp : ∀ (ω : Ω) (D₁ D₂ : Place → ℤ) (P : Place),
      omegaD ω D₁ → omegaD ω D₂ → D₁ P < D₂ P →
      omegaD ω (addPlace D₁ P))
    (ω : Ω) (hω : ω ≠ 0)
    (hex : ∃ D, omegaD ω D)
    (hfin : Set.Finite {D | omegaD ω D}) :
    ∃! D, IsMaximalDivisorFor omegaD ω D := by
  obtain ⟨D, hD⟩ := exists_maximal_divisor omegaD adele_decomp ω hω hex hfin
  exact ⟨D, hD, fun D' hD' => unique_maximal_divisor omegaD ω hD' hD⟩

end Lemma22_15
