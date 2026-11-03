/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.HomologySequence

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace LongExactCohomology

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The cochain shape relates `n` to `n + 1`. -/
lemma up_rel (n : ℤ) : (ComplexShape.up ℤ).Rel n (n + 1) := rfl

/-- The connecting homomorphism `H^n(C) → H^{n+1}(A)` in cohomology arising from
a short exact sequence of cochain complexes. -/
def connectingHomomorphism
    {S : CategoryTheory.ShortComplex (CochainComplex 𝒜 ℤ)}
    (hS : S.ShortExact) (n : ℤ) :
    S.X₃.homology n ⟶ S.X₁.homology (n + 1) :=
  hS.δ n (n + 1) (up_rel n)

/-- Exactness of the long exact cohomology sequence at `H^{n+1}(A)`
(Prop 42, Lec 23). -/
theorem long_exact_seq_exact_at_H_A
    {S : CategoryTheory.ShortComplex (CochainComplex 𝒜 ℤ)}
    (hS : S.ShortExact) (n : ℤ) :
    (CategoryTheory.ShortComplex.mk
      (connectingHomomorphism hS n)
      (HomologicalComplex.homologyMap S.f (n + 1))
      (hS.δ_comp n (n + 1) (up_rel n))).Exact :=
  hS.homology_exact₁ n (n + 1) (up_rel n)

/-- Exactness of the long exact cohomology sequence at `H^n(B)`. -/
theorem long_exact_seq_exact_at_H_B
    {S : CategoryTheory.ShortComplex (CochainComplex 𝒜 ℤ)}
    (hS : S.ShortExact) (n : ℤ) :
    (CategoryTheory.ShortComplex.mk
      (HomologicalComplex.homologyMap S.f n)
      (HomologicalComplex.homologyMap S.g n)
      (by rw [← HomologicalComplex.homologyMap_comp, S.zero,
              HomologicalComplex.homologyMap_zero])).Exact :=
  CategoryTheory.ShortComplex.ShortExact.homology_exact₂ hS n

/-- Exactness of the long exact cohomology sequence at `H^n(C)`. -/
theorem long_exact_seq_exact_at_H_C
    {S : CategoryTheory.ShortComplex (CochainComplex 𝒜 ℤ)}
    (hS : S.ShortExact) (n : ℤ) :
    (CategoryTheory.ShortComplex.mk
      (HomologicalComplex.homologyMap S.g n)
      (connectingHomomorphism hS n)
      (hS.comp_δ n (n + 1) (up_rel n))).Exact :=
  hS.homology_exact₃ n (n + 1) (up_rel n)

/-- The long exact cohomology sequence: from a short exact sequence of cochain
complexes, exactness holds at `H^n(B)`, `H^n(C)`, and `H^{n+1}(A)` (the snake
lemma, Prop 42, Lec 23). -/
theorem long_exact_cohomology_sequence
    {S : CategoryTheory.ShortComplex (CochainComplex 𝒜 ℤ)}
    (hS : S.ShortExact) (n : ℤ) :

    (CategoryTheory.ShortComplex.mk
      (HomologicalComplex.homologyMap S.f n)
      (HomologicalComplex.homologyMap S.g n)
      (by rw [← HomologicalComplex.homologyMap_comp, S.zero,
              HomologicalComplex.homologyMap_zero])).Exact

    ∧ (CategoryTheory.ShortComplex.mk
        (HomologicalComplex.homologyMap S.g n)
        (connectingHomomorphism hS n)
        (hS.comp_δ n (n + 1) (up_rel n))).Exact

    ∧ (CategoryTheory.ShortComplex.mk
        (connectingHomomorphism hS n)
        (HomologicalComplex.homologyMap S.f (n + 1))
        (hS.δ_comp n (n + 1) (up_rel n))).Exact :=
  ⟨long_exact_seq_exact_at_H_B hS n,
   long_exact_seq_exact_at_H_C hS n,
   long_exact_seq_exact_at_H_A hS n⟩

end LongExactCohomology
