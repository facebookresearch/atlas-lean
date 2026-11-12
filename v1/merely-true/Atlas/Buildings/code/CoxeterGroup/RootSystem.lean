/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation

open Finset BigOperators

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- A vector $\alpha$ is a root iff it lies in the $W$-orbit of some simple root $e_s$,
i.e. there is a word $w$ and simple $s$ with $\alpha = w \cdot e_s$. -/
def isRoot (M : CoxeterMatrix B) (α : B → ℝ) : Prop :=
  ∃ (word : List B) (s : B), α = wordSigma M word (e s)

/-- Simple reflections $\sigma_s$ map roots to roots: the root system is $W$-stable. -/
theorem sigma_maps_roots (M : CoxeterMatrix B) (s : B) (α : B → ℝ) (hα : isRoot M α) :
    isRoot M (sigma M s α) := by
  obtain ⟨word, t, rfl⟩ := hα
  exact ⟨s :: word, t, rfl⟩

/-- A vector is strictly positive at some coordinate: $\exists s,\, v(s) > 0$. -/
def isPositiveVec (v : B → ℝ) : Prop := ∃ s : B, v s > 0

/-- A vector is strictly negative at some coordinate: $\exists s,\, v(s) < 0$. -/
def isNegativeVec (v : B → ℝ) : Prop := ∃ s : B, v s < 0

/-- The vector $-e_s$ is strictly negative at coordinate $s$. -/
theorem neg_e_isNegative (s : B) : isNegativeVec (fun t => -(e s t)) :=
  ⟨s, by simp [e, Pi.single_apply, if_pos rfl]⟩

/-- For $s \ne t$, the $t$-coordinate of $\sigma_s(e_t)$ equals $1$. -/
theorem sigma_e_other_t_component (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t) :
    sigma M s (e t) t = 1 := by
  simp only [sigma, bilinForm_e_e]
  simp only [e, Pi.single_apply, if_true, if_neg (Ne.symm hst)]
  ring

/-- The set of simple generators $s$ such that the $s$-coordinate of $w \cdot e_s$ is strictly
negative — the simple inversions of the word. -/
def simpleInversions (M : CoxeterMatrix B) (word : List B) : Set B :=
  { s | wordSigma M word (e s) s < 0 }

/-- The action of the word $w$ on $\mathbb{R}^B$ packaged as an $\mathbb{R}$-linear map. -/
noncomputable def wordSigmaLinearMap (M : CoxeterMatrix B) (word : List B) :
    (B → ℝ) →ₗ[ℝ] (B → ℝ) where
  toFun := wordSigma M word
  map_add' := wordSigma_add M word
  map_smul' := wordSigma_smul M word

/-- Reversing a word inverts its geometric action: $w \cdot (w^{-1} \cdot v) = v$. -/
theorem wordSigma_reverse_cancel (M : CoxeterMatrix B) (word : List B) (v : B → ℝ) :
    wordSigma M word (wordSigma M word.reverse v) = v := by
  induction word generalizing v with
  | nil => simp
  | cons s rest ih =>
    simp only [wordSigma_cons, List.reverse_cons, wordSigma_append, wordSigma_singleton,
      wordSigma_nil]
    rw [ih]
    exact sigma_involution M s v

end CoxeterGroup
