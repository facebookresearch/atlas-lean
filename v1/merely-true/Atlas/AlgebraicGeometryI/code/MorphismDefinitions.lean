/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.KrullDimension.Basic
import Atlas.AlgebraicGeometryI.code.FiniteMorphismDimension

open PrimeSpectrum

namespace MorphismDefinitions

section FiniteAlgebra

variable (B A : Type*) [CommRing B] [CommRing A] [Algebra B A]

/-- A `B`-algebra `A` is finite if `A` is a finitely generated `B`-module. -/
abbrev IsFiniteAlgebra : Prop := Module.Finite B A

/-- A finite algebra is integral. -/
theorem isFiniteAlgebra_isIntegral [Module.Finite B A] : Algebra.IsIntegral B A :=
  Algebra.IsIntegral.of_finite B A

end FiniteAlgebra

section Lemma7

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- A finite morphism of rings induces a closed map on prime spectra (Lec 3–4). -/
theorem finite_morphism_isClosedMap [Module.Finite B A] :
    IsClosedMap (PrimeSpectrum.comap (algebraMap B A)) := by
  have hIntegral : (algebraMap B A).IsIntegral := fun x =>
    (Algebra.IsIntegral.of_finite B A).isIntegral x
  exact PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap B A) hIntegral

/-- A finite morphism has finite fibers on prime spectra. -/
theorem finite_morphism_finite_fibers [Module.Finite B A] (𝔭 : PrimeSpectrum B) :
    Set.Finite (PrimeSpectrum.comap (algebraMap B A) ⁻¹' {𝔭}) :=
  Algebra.QuasiFinite.finite_comap_preimage_singleton 𝔭

end Lemma7

section Corollary9

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- A finite injective morphism of rings is surjective on prime spectra
(Corollary 9). -/
theorem finite_morphism_surjective_on_spec [Module.Finite B A]
    (hinj : Function.Injective (algebraMap B A)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap B A)) := by
  have hIntegral : (algebraMap B A).IsIntegral := fun x =>
    (Algebra.IsIntegral.of_finite B A).isIntegral x
  exact hIntegral.comap_surjective hinj

/-- For a finite injective morphism, each fiber on prime spectra is finite and
nonempty. -/
theorem finite_morphism_fiber_finite_nonempty [Module.Finite B A]
    (hinj : Function.Injective (algebraMap B A)) (𝔭 : PrimeSpectrum B) :
    (PrimeSpectrum.comap (algebraMap B A) ⁻¹' {𝔭}).Finite ∧
    (PrimeSpectrum.comap (algebraMap B A) ⁻¹' {𝔭}).Nonempty := by
  refine ⟨finite_morphism_finite_fibers 𝔭, ?_⟩
  obtain ⟨q, hq⟩ := finite_morphism_surjective_on_spec hinj 𝔭
  exact ⟨q, hq ▸ Set.mem_preimage.mpr rfl⟩

end Corollary9

section DimensionPreservation

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- A finite injective morphism of rings preserves Krull dimension. -/
theorem finite_morphism_dim_eq [Module.Finite B A]
    (hinj : Function.Injective (algebraMap B A)) :
    ringKrullDim A = ringKrullDim B :=
  FiniteMorphismDimension.ringKrullDim_eq_of_injective_finite hinj

end DimensionPreservation

end MorphismDefinitions
