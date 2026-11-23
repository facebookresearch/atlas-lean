/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.Analysis.Complex.Basic

namespace RepresentationTheory

open Representation

universe u

theorem maschke_complement {k G : Type*} [Field k] [Group G] [Finite G]
    [NeZero (Nat.card G : k)]
    {V : Type*} [AddCommGroup V] [Module (MonoidAlgebra k G) V]
    (p : Submodule (MonoidAlgebra k G) V) :
    ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q :=
  MonoidAlgebra.Submodule.exists_isCompl p

theorem maschke_semisimple {k G V : Type*} [Field k] [Group G] [Finite G]
    [NeZero (Nat.card G : k)] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    ρ.IsSemisimpleRepresentation :=
  inferInstance

theorem maschke_semisimple_complex {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.IsSemisimpleRepresentation := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  exact maschke_semisimple ρ

def IsIrreducible {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : Prop :=
  IsSimpleOrder (Subrepresentation ρ)

noncomputable def characterOf {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) : G → k :=
  ρ.character

noncomputable def directSumPair {k G V W : Type*} [Semiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (ρV : Representation k G V) (ρW : Representation k G W) :
    Representation k G (V × W) :=
  Representation.prod ρV ρW

section SchurLemma

open CategoryTheory Module

variable {k G : Type u} [Field k] [Group G]
