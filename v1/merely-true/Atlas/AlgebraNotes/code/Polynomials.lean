/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Polynomials

abbrev IsPrimitivePolynomial {R : Type*} [CommSemiring R] (p : Polynomial R) : Prop :=
  p.IsPrimitive

instance polynomialUFD (F : Type*) [Field F] : UniqueFactorizationMonoid (Polynomial F) :=
  inferInstance

noncomputable def evalRingHom (R : Type*) [CommRing R] (α : R) : Polynomial R →+* R :=
  Polynomial.evalRingHom α

open MvPolynomial in
theorem polynomial_mapping_property
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {σ : Type*} (α : σ → S) :
    (∃! ψ : MvPolynomial σ R →+* S,
      (∀ r : R, ψ (MvPolynomial.C r) = φ r) ∧
      (∀ i : σ, ψ (MvPolynomial.X i) = α i)) := by
  refine ⟨eval₂Hom φ α, ⟨eval₂Hom_C φ α, eval₂Hom_X' φ α⟩, ?_⟩
  intro ψ ⟨hC, hX⟩
  exact ringHom_ext (fun r => by rw [hC, eval₂Hom_C]) (fun i => by rw [hX, eval₂Hom_X'])

end Polynomials
