/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace LongExactSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type*} {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}


/-- The connecting homomorphism `H_i(C) → H_j(A)` of the long exact homology
sequence arising from a short exact sequence of complexes. -/
def cohomologyδ (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  hS.δ i j hij


/-- Exactness of the long exact sequence at `H_i(B)`. -/
theorem long_exact_sequence_exact_at_Hi_B (hS : S.ShortExact) (i : ι) :
    (ShortComplex.mk
      (homologyMap S.f i)
      (homologyMap S.g i)
      (by rw [← homologyMap_comp, S.zero, homologyMap_zero])).Exact :=
  hS.homology_exact₂ i

/-- Exactness of the long exact sequence at `H_i(C)`. -/
theorem long_exact_sequence_exact_at_Hi_C (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (hS.comp_δ i j hij)).Exact :=
  hS.homology_exact₃ i j hij

/-- Exactness of the long exact sequence at `H_j(A)`. -/
theorem long_exact_sequence_exact_at_Hj_A (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (hS.δ_comp i j hij)).Exact :=
  hS.homology_exact₁ i j hij


/-- The long exact (co)homology sequence: from a short exact sequence of complexes,
exactness holds at `H_i(B)`, `H_i(C)`, and `H_j(A)`. -/
theorem long_exact_sequence (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :

    (ShortComplex.mk
      (homologyMap S.f i)
      (homologyMap S.g i)
      (by rw [← homologyMap_comp, S.zero, homologyMap_zero])).Exact

    ∧ (ShortComplex.mk _ _ (hS.comp_δ i j hij)).Exact

    ∧ (ShortComplex.mk _ _ (hS.δ_comp i j hij)).Exact :=
  ⟨hS.homology_exact₂ i, hS.homology_exact₃ i j hij, hS.homology_exact₁ i j hij⟩


/-- If `H_i(B) = 0`, the connecting homomorphism `δ` is a monomorphism. -/
theorem mono_cohomologyδ (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
    (hi : IsZero (S.X₂.homology i)) : Mono (cohomologyδ hS i j hij) :=
  hS.mono_δ i j hij hi

/-- If `H_j(B) = 0`, the connecting homomorphism `δ` is an epimorphism. -/
theorem epi_cohomologyδ (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
    (hj : IsZero (S.X₂.homology j)) : Epi (cohomologyδ hS i j hij) :=
  hS.epi_δ i j hij hj

/-- If both `H_i(B)` and `H_j(B)` vanish, the connecting `δ` is an isomorphism. -/
theorem isIso_cohomologyδ (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
    (hi : IsZero (S.X₂.homology i)) (hj : IsZero (S.X₂.homology j)) :
    IsIso (cohomologyδ hS i j hij) :=
  hS.isIso_δ i j hij hi hj

end LongExactSequence
