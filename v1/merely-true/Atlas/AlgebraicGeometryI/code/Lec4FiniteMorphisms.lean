/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.Topology.KrullDimension

open AlgebraicGeometry PrimeSpectrum TopologicalSpace Set

universe u

namespace Lec4

/-- Lecture 4, Definition 9: affine morphism of schemes, defined here in terms of Mathlib's
`IsAffineHom`. -/
abbrev IsAffineMorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  IsAffineHom f

/-- Lecture 4, Definition 10: a *finite morphism* of schemes, defined here as Mathlib's
`IsFinite f`. -/
abbrev IsFiniteMorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  IsFinite f

/-- Lecture 4, Lemma 7 (closedness part): a finite morphism of schemes is a closed map. -/
theorem finiteMorphism_closedMap {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] :
    IsClosedMap f :=
  f.isClosedMap

/-- Lecture 4, Lemma 7 (finite-fibers part): a finite morphism has finite fibers. -/
theorem finiteMorphism_finitePreimage {X Y : Scheme} (f : X ⟶ Y) [IsFinite f]
    (y : Y) : (f ⁻¹' {y}).Finite :=
  f.finite_preimage_singleton y

/-- Ring-theoretic version of Lecture 4, Corollary 9: if `A` is a finite injective `B`-algebra,
then `Spec A → Spec B` is surjective. -/
theorem comap_surjective_of_finite_injective
    {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    [Module.Finite B A] (hinj : Function.Injective (algebraMap B A)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap B A)) := by
  have hInt : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  exact (algebraMap_isIntegral_iff.mpr hInt).comap_surjective hinj

/-- Ring-theoretic version of finite fibers: for a finite `B`-algebra `A`, the map
`Spec A → Spec B` has finite fibers. -/
theorem comap_finite_fibers_of_finite
    {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    [Module.Finite B A] (p : PrimeSpectrum B) :
    (PrimeSpectrum.comap (algebraMap B A) ⁻¹' {p}).Finite :=
  Algebra.QuasiFinite.finite_comap_preimage_singleton p

/-- "Incomparability" for finite extensions: for `A` finite over `B`, a strict containment of
primes `I < J` in `A` contracts to a strict containment in `B`. -/
theorem comap_lt_comap_of_finite
    {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    [Module.Finite B A]
    {I J : Ideal A} [I.IsPrime]
    (hIJ : I < J) :
    Ideal.comap (algebraMap B A) I < Ideal.comap (algebraMap B A) J := by

  have hInt : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A

  obtain ⟨x, hxJ, hxI⟩ := Set.exists_of_ssubset hIJ

  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hIJ.le ⟨hxJ, hxI⟩
    (Algebra.IsIntegral.isIntegral x)

/-- Convenience wrapper: the topological Krull dimension of `T`, used here as the Lec 4 notion
of dimension. -/
noncomputable abbrev krullDim_def (T : Type*) [TopologicalSpace T] : WithBot ℕ∞ :=
  topologicalKrullDim T

end Lec4
