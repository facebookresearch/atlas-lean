/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.CompletenessValuationCriterion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

universe u

open AlgebraicGeometry

/-- (Lemma 16.32) Given a valuation subring $R \subseteq F$ and finitely many nonzero $x_0, \dots, x_n \in F$, there exists $\lambda \in F^\times$ such that $\lambda x_i \in R$ for all $i$ and some $\lambda x_i$ is a unit in $R$ (this normalises projective coordinates with respect to a valuation). -/
theorem lemma_16_32 {F : Type*} [Field F] (R : ValuationSubring F)
    (n : ℕ) (x : Fin (n + 1) → F) (hx : ∀ i, x i ≠ 0) :
    ∃ (l : F), l ≠ 0 ∧ (∀ i, l * x i ∈ (R : Set F)) ∧
      (∃ i, (l * x i)⁻¹ ∈ (R : Set F)) := by
  induction n with
  | zero =>
    refine ⟨(x 0)⁻¹, inv_ne_zero (hx 0), ?_, ⟨0, ?_⟩⟩
    · intro i
      have hi : i = 0 := by ext; omega
      subst hi; simp [inv_mul_cancel₀ (hx 0)]
    · simp [inv_mul_cancel₀ (hx 0)]
  | succ m ih =>
    let x' : Fin (m + 1) → F := fun i => x (Fin.castSucc i)
    have hx' : ∀ i, x' i ≠ 0 := fun i => hx (Fin.castSucc i)
    obtain ⟨l, hl_ne, hl_mem, ⟨j, hj_inv⟩⟩ := ih x' hx'
    by_cases hlast : l * x (Fin.last (m + 1)) ∈ (R : Set F)
    ·
      refine ⟨l, hl_ne, ?_, ⟨Fin.castSucc j, hj_inv⟩⟩
      intro i
      by_cases hi : (i : ℕ) < m + 1
      · rw [show i = Fin.castSucc (⟨i, hi⟩ : Fin (m + 1)) from by ext; simp]
        exact hl_mem ⟨i, hi⟩
      · rw [show i = Fin.last (m + 1) from by ext; simp; omega]; exact hlast
    ·

      have hlast_inv : (l * x (Fin.last (m + 1)))⁻¹ ∈ (R : Set F) :=
        (R.mem_or_inv_mem _).resolve_left hlast
      refine ⟨(x (Fin.last (m + 1)))⁻¹, inv_ne_zero (hx _), ?_,
              ⟨Fin.last (m + 1), by simp [inv_mul_cancel₀ (hx _)]⟩⟩
      intro i
      by_cases hi : (i : ℕ) < m + 1
      ·
        rw [show i = Fin.castSucc (⟨i, hi⟩ : Fin (m + 1)) from by ext; simp]
        suffices h : (x (Fin.last (m + 1)))⁻¹ * x (Fin.castSucc ⟨i, hi⟩) =
            l * x (Fin.castSucc ⟨i, hi⟩) * (l * x (Fin.last (m + 1)))⁻¹ by
          rw [h]; exact R.toSubring.mul_mem (hl_mem ⟨i, hi⟩) hlast_inv
        field_simp
      ·
        rw [show i = Fin.last (m + 1) from by ext; simp; omega]
        rw [inv_mul_cancel₀ (hx _)]; exact R.one_mem'

namespace AlgebraicGeometry.CompletenessValuationCriterion

/-- A projective variety structure on $V$: a choice of dimension $n$ and homogeneous coordinates $X_0, \dots, X_n \in K(Z)^\times$ (none vanishing) on every subvariety $Z$ of $V$. -/
structure IsProjectiveVariety {k : Type u} [Field k] (V : AlgVariety k) where
  n : ℕ
  homogCoords : (Z : SubvarietyOf V) → Fin (n + 1) → Z.toVariety.functionField
  homogCoords_ne_zero : ∀ (Z : SubvarietyOf V) (i : Fin (n + 1)),
    homogCoords Z i ≠ 0





end AlgebraicGeometry.CompletenessValuationCriterion

/-- (Theorem 16.33) The structure morphism $\mathrm{Proj}\,\mathcal{A} \to \mathrm{Spec}\,\mathcal{A}_0$ from a finitely generated $\mathbb{N}$-graded ring is proper. -/
theorem theorem_16_33
    {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A] :
    IsProper (Proj.toSpecZero 𝒜) :=
  inferInstance
