/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Smooth.Basic

noncomputable section

open scoped TensorProduct
open KaehlerDifferential

universe u

section CotangentExactSequence

variable (R : Type u) [CommRing R]
variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- Proposition 35 (Lec 20): exactness in the middle of the conormal sequence
`I/I² → B ⊗_A Ω_{A/R} → Ω_{B/R} → 0` when `A → B` is surjective. -/
theorem conormalExactSeq_exact
    (h : Function.Surjective (algebraMap A B)) :
    Function.Exact
      (KaehlerDifferential.kerCotangentToTensor R A B)
      (KaehlerDifferential.mapBaseChange R A B) :=
  KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h

/-- The right-hand map `B ⊗_A Ω_{A/R} → Ω_{B/R}` in the conormal sequence is surjective when
`A → B` is surjective. -/
theorem conormalExactSeq_mapBaseChange_surjective
    (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (KaehlerDifferential.mapBaseChange R A B) :=
  KaehlerDifferential.mapBaseChange_surjective R A B h

/-- Right exactness of the conormal sequence: combines the exactness at the middle with the
surjectivity on the right. -/
theorem conormalExactSeq_rightExact
    (h : Function.Surjective (algebraMap A B)) :
    Function.Exact
      (KaehlerDifferential.kerCotangentToTensor R A B)
      (KaehlerDifferential.mapBaseChange R A B) ∧
    Function.Surjective (KaehlerDifferential.mapBaseChange R A B) :=
  ⟨KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h,
   KaehlerDifferential.mapBaseChange_surjective R A B h⟩

/-- Under formal smoothness of both `A/R` and `B/R`, the conormal sequence is a short exact
sequence: the map `I/I² → B ⊗_A Ω_{A/R}` is also injective. -/
theorem conormalExactSeq_shortExact_of_formallySmooth
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R B]
    (h : Function.Surjective (algebraMap A B)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor R A B) ∧
    Function.Exact
      (KaehlerDifferential.kerCotangentToTensor R A B)
      (KaehlerDifferential.mapBaseChange R A B) ∧
    Function.Surjective (KaehlerDifferential.mapBaseChange R A B) := by
  refine ⟨?_, KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h,
    KaehlerDifferential.mapBaseChange_surjective R A B h⟩
  rw [Algebra.FormallySmooth.kerCotangentToTensor_injective_iff h]
  infer_instance

/-- Under formal smoothness, the inclusion `I/I² → B ⊗_A Ω_{A/R}` admits a left inverse, so the
conormal sequence is a *split* short exact sequence. -/
theorem conormalExactSeq_splitInjection
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R B]
    (h : Function.Surjective (algebraMap A B)) :
    ∃ l : (B ⊗[A] Ω[A⁄R]) →ₗ[A] (RingHom.ker (algebraMap A B)).Cotangent,
      l ∘ₗ (KaehlerDifferential.kerCotangentToTensor R A B) = LinearMap.id :=
  (Algebra.FormallySmooth.iff_split_injection h).mp inferInstance


end CotangentExactSequence

section Corollary26

variable (R : Type u) [CommRing R]
variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- Corollary 26: under formal smoothness, the conormal sequence is short exact. -/
theorem conormalSequence_shortExact_of_smooth
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R B]
    (h : Function.Surjective (algebraMap A B)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor R A B) ∧
    Function.Exact
      (KaehlerDifferential.kerCotangentToTensor R A B)
      (KaehlerDifferential.mapBaseChange R A B) ∧
    Function.Surjective (KaehlerDifferential.mapBaseChange R A B) := by
  refine ⟨?_, KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h,
    KaehlerDifferential.mapBaseChange_surjective R A B h⟩
  rw [Algebra.FormallySmooth.kerCotangentToTensor_injective_iff h]
  infer_instance

end Corollary26

end
