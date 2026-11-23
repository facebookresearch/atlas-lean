/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Polynomial.Basic

open AlgebraicGeometry PrimeSpectrum

section GlobalSections

/-- Theorem 2.1: the global sections of `Spec R` recover `R`, i.e. `Γ(Spec R, O) ≅ R`. -/
noncomputable def globalSections_spec_iso (R : CommRingCat.{u}) :
    Γ(Spec R, ⊤) ≅ R :=
  Scheme.ΓSpecIso R

end GlobalSections

section QuasiCompact

/-- `Spec R` is quasi-compact: the prime spectrum of any commutative ring is compact. -/
theorem specQuasiCompact (R : Type*) [CommRing R] : CompactSpace (PrimeSpectrum R) :=
  PrimeSpectrum.compactSpace

end QuasiCompact

section ClosedSubspace

/-- The closed subspace `Spec(A/I) → Spec A` arising from a quotient ring is a closed
topological embedding. -/
theorem closedSubspace_isClosedEmbedding (A : Type*) [CommRing A] (I : Ideal A) :
    Topology.IsClosedEmbedding
      (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
  PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
    Ideal.Quotient.mk_surjective

/-- The image of `Spec(A/I) → Spec A` is the zero locus `V(I)` of the ideal `I`. -/
theorem closedSubspace_range_eq_zeroLocus (A : Type*) [CommRing A] (I : Ideal A) :
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set A) := by
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
  congr 1
  ext x
  simp

end ClosedSubspace

section HilbertBasis

/-- Hilbert basis theorem: polynomials over a Noetherian ring in finitely many variables form a
Noetherian ring. -/
theorem hilbertBasisTheorem_mv (k : Type*) [CommRing k] [IsNoetherianRing k] (n : ℕ) :
    IsNoetherianRing (MvPolynomial (Fin n) k) :=
  MvPolynomial.isNoetherianRing_fin

/-- Hilbert basis theorem specialized to a field: `k[x_1, …, x_n]` is Noetherian. -/
theorem hilbertBasisTheorem_field (k : Type*) [Field k] (n : ℕ) :
    IsNoetherianRing (MvPolynomial (Fin n) k) :=
  MvPolynomial.isNoetherianRing_fin

end HilbertBasis
