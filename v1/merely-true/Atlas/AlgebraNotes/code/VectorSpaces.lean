/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Module

namespace VectorSpaces

open Submodule

variable {ι : Type*} {R : Type*} {M : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M]

theorem basis_iff (v : ι → M) :
    (∃ b : Basis ι R M, ⇑b = v) ↔
      (LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤) := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.linearIndependent, b.span_eq⟩
  · rintro ⟨hli, hsp⟩
    exact ⟨Basis.mk hli (le_of_eq hsp.symm), Basis.coe_mk hli _⟩

section BasisExtension

open Set Module

variable {K : Type u} {V : Type u} [DivisionRing K] [AddCommGroup V] [Module K V]

theorem basis_extension_lemma (S : Set V) (L : Set V)
    (hS : ⊤ ≤ span K S) (hL : LinearIndepOn K id L) [Fintype ↥S] [Fintype ↥L] :
    (∃ (ι' : Type u) (b : Basis ι' K V), Set.range b ⊆ S) ∧
    (∃ (ι' : Type u) (b : Basis ι' K V), L ⊆ Set.range b ∧ Set.range b ⊆ L ∪ S) ∧
    (Fintype.card ↥L ≤ Fintype.card ↥S) := by
  refine ⟨⟨_, Basis.ofSpan hS, Basis.ofSpan_subset hS⟩, ?_, ?_⟩
  · have hLS : L ⊆ L ∪ S := Set.subset_union_left
    have hSpan : ⊤ ≤ span K (L ∪ S) := le_trans hS (Submodule.span_mono Set.subset_union_right)
    exact ⟨_, Basis.extendLe hL hLS hSpan,
      Basis.subset_extendLe hL hLS hSpan,
      Basis.extendLe_subset hL hLS hSpan⟩
  · have hli : LinearIndependent K (Subtype.val : ↥L → V) := by
      have := hL.linearIndependent_restrict
      convert this using 1
    have hle := linearIndependent_le_span (Subtype.val : ↥L → V) hli S (by rwa [eq_top_iff])
    simp only [Cardinal.mk_fintype] at hle
    exact_mod_cast hle

end BasisExtension

end VectorSpaces
