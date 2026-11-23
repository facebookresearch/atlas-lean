/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.IntegralDomain
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement

namespace FiniteFields

theorem finite_field_units_cyclic (F : Type*) [Field F] (G : Subgroup Fˣ) [Finite ↥G] :
    IsCyclic ↥G := inferInstance

theorem finite_field_existence_uniqueness (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n ≠ 0) :

    Nat.card (GaloisField p n) = p ^ n ∧

    ∀ (K : Type*) [Field K] [Algebra (ZMod p) K],
      Nat.card K = p ^ n → Nonempty (K ≃ₐ[ZMod p] GaloisField p n) := by
  constructor
  · exact GaloisField.card p n hn
  · intro K _ _ hK
    exact ⟨GaloisField.algEquivGaloisField p n hK⟩

open Polynomial IntermediateField Module

theorem finite_field_simple_extension_and_irreducibles
    (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 0 < n) :

    (∃ α : GaloisField p n, (ZMod p)⟮α⟯ = ⊤) ∧

    (∃ f : Polynomial (ZMod p), Irreducible f ∧ f.natDegree = n) := by
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  constructor
  ·
    exact Field.exists_primitive_element_of_finite_top (ZMod p) (GaloisField p n)
  ·
    obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top (ZMod p) (GaloisField p n)
    refine ⟨minpoly (ZMod p) α, minpoly.irreducible (IsIntegral.of_finite _ _), ?_⟩
    have h1 := (Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) α).mp hα
    rw [h1, GaloisField.finrank p hne]

end FiniteFields
