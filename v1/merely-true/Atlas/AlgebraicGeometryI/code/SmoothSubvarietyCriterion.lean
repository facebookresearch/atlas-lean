/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.FinitePresentation

universe u v w

open scoped TensorProduct
open KaehlerDifferential Algebra

variable {R : Type u} {A : Type v} {B : Type w}
  [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- Predicate asserting that the canonical map from the cotangent module of
the kernel `I = ker(A → B)` to `B ⊗_A Ω[A/R]` has a left inverse, i.e. that the
differentials of generators of `I` are linearly independent in `B ⊗_A Ω[A/R]`. -/
def HasLinearlyIndependentDifferentials (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] : Prop :=
  ∃ l : B ⊗[A] Ω[A⁄R] →ₗ[A] (RingHom.ker (algebraMap A B)).Cotangent,
    l ∘ₗ kerCotangentToTensor R A B = LinearMap.id

/-- Formally-smooth version of the smooth subvariety criterion: assuming `A`
is formally smooth over `R` and `A → B` is surjective, `B` is formally smooth
over `R` iff the defining ideal has linearly independent differentials. -/
theorem smooth_subvariety_criterion_formallySmooth
    [FormallySmooth R A]
    (hf : Function.Surjective (algebraMap A B)) :
    FormallySmooth R B ↔ HasLinearlyIndependentDifferentials R A B :=
  FormallySmooth.iff_split_injection hf

/-- Smooth subvariety criterion (Cor 25, Lec 20): if `A` is smooth over `R`
and `A → B` is surjective with finitely generated kernel, then `B` is smooth
over `R` iff the kernel has linearly independent differentials, i.e. iff the
subvariety is locally defined by independent differentials. -/
theorem smooth_subvariety_criterion
    [Smooth R A]
    (hf : Function.Surjective (algebraMap A B))
    (hker : (RingHom.ker (algebraMap A B)).FG) :
    Smooth R B ↔ HasLinearlyIndependentDifferentials R A B := by
  constructor
  ·
    intro hB
    haveI : FormallySmooth R B := Smooth.formallySmooth
    exact (FormallySmooth.iff_split_injection hf).mp inferInstance
  ·
    intro h
    haveI : FormallySmooth R A := Smooth.formallySmooth
    haveI : FormallySmooth R B := (FormallySmooth.iff_split_injection hf).mpr h
    haveI : FinitePresentation R A := Smooth.finitePresentation
    haveI : FinitePresentation R B :=
      FinitePresentation.of_surjective (f := IsScalarTower.toAlgHom R A B) hf hker
    exact ⟨inferInstance, inferInstance⟩
