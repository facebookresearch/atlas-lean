/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.Locus

noncomputable section

open AlgebraicGeometry Algebra

universe u

variable {X : Scheme.{u}} {K : Type u} [Field K]

/-- The **singular locus** of a morphism `f : X → Spec K` is the complement of
the smooth locus, i.e., the set of points where `f` fails to be smooth. -/
def singularLocus (f : X ⟶ Spec (.of K))
    [LocallyOfFinitePresentation f] : Set X :=
  (f.smoothLocus : Set X)ᶜ

/-- The singular locus is closed: smoothness is an open condition. -/
theorem singularLocus_isClosed (f : X ⟶ Spec (.of K))
    [LocallyOfFinitePresentation f] :
    IsClosed (singularLocus f) :=
  f.isOpen_smoothLocus.isClosed_compl

/-- **Singular locus is not everything** for a reduced scheme over a perfect
field: a non-empty reduced scheme of finite presentation has a non-empty smooth
locus, so its singular locus is a proper subset. This is generic smoothness in
the perfect-field case. -/
theorem singularLocus_ne_univ [PerfectField K] [IsReduced X] [Nonempty X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    singularLocus f ≠ Set.univ := by
  intro h
  have hempty : (f.smoothLocus : Set X) = ∅ := Set.compl_univ_iff.mp h
  have hd := f.dense_smoothLocus_of_perfectField
  rw [hempty] at hd
  have h1 := hd.closure_eq
  simp at h1
  exact Set.empty_ne_univ h1

variable {A : Type*} [CommRing A] [Algebra K A]

/-- Algebraic version of `singularLocus`: for a `K`-algebra `A`, the singular
locus is the complement of the smooth locus inside `Spec A`. -/
def singularLocusAlg (K : Type*) [Field K] (A : Type*) [CommRing A]
    [Algebra K A] : Set (PrimeSpectrum A) :=
  (Algebra.smoothLocus K A)ᶜ

/-- The algebraic singular locus is closed when `A` is finitely presented over `K`. -/
theorem singularLocusAlg_isClosed [FinitePresentation K A] :
    IsClosed (singularLocusAlg K A) :=
  isOpen_smoothLocus.isClosed_compl

end
