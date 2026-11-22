/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Rings

universe u

theorem ring_product_iff_nontrivial_idempotent (Q : Type u) [CommRing Q] :
    (∃ (R S : Type u) (_ : Ring R) (_ : Ring S) (_ : Nontrivial R) (_ : Nontrivial S),
      Nonempty (Q ≃+* R × S)) ↔
    (∃ e : Q, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1) := by
  constructor
  ·
    rintro ⟨R, S, _, _, hR, hS, ⟨φ⟩⟩
    refine ⟨φ.symm (1, 0), ?_, ?_, ?_⟩
    ·
      rw [IsIdempotentElem, ← map_mul φ.symm]
      congr 1
      simp
    ·
      intro h
      have := congr_arg φ h
      simp at this
    ·
      intro h
      have := congr_arg φ h
      simp at this
  ·
    rintro ⟨e, he, he0, he1⟩
    have hf : IsIdempotentElem (1 - e) := he.one_sub
    have hef1 : e + (1 - e) = 1 := by ring
    have hef2 : e * (1 - e) = 0 := by
      have h := he.eq
      have : e * (1 - e) = e - e * e := by ring
      rw [this, h, sub_self]

    have hne_top : Ideal.span {e} ≠ ⊤ := by
      intro htop
      rw [Ideal.span_singleton_eq_top] at htop
      exact he1 ((IsIdempotentElem.iff_eq_one_of_isUnit htop).mp he)

    have hne_top' : Ideal.span {(1 : Q) - e} ≠ ⊤ := by
      intro htop
      rw [Ideal.span_singleton_eq_top] at htop
      have h1 : (1 : Q) - e = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit htop).mp hf
      have h2 : (1 : Q) - e - 1 = 0 := by rw [h1]; ring
      have h3 : -(e : Q) = 0 := by ring_nf at h2 ⊢; exact h2
      exact he0 (neg_eq_zero.mp h3)

    exact ⟨Q ⧸ Ideal.span {e}, Q ⧸ Ideal.span {1 - e}, inferInstance, inferInstance,
      Ideal.Quotient.nontrivial_iff.mpr hne_top, Ideal.Quotient.nontrivial_iff.mpr hne_top',
      ⟨(AlgEquiv.prodQuotientOfIsIdempotentElem ℤ he hf hef1 hef2).toRingEquiv⟩⟩

end Rings
