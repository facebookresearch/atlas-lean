/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Constructions
import Mathlib.Order.Directed

namespace TopologicalSpace.DirectLimit

section BasicDefs

variable {ι : Type*} [Preorder ι]
  (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
  (f : ∀ i j, i ≤ j → X i → X j)

def Rel : (Σ i, X i) → (Σ i, X i) → Prop :=
  fun a b => ∃ (i j : ι) (h : i ≤ j) (x : X i),
    a = ⟨i, x⟩ ∧ b = ⟨j, f i j h x⟩

def directLimitSetoid : Setoid (Σ i, X i) :=
  Relation.EqvGen.setoid (Rel X f)

end BasicDefs

abbrev Space {ι : Type*} [Preorder ι]
    (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    (f : ∀ i j, i ≤ j → X i → X j) : Type _ :=
  @Quotient (Σ i, X i) (directLimitSetoid X f)

section Maps

variable {ι : Type*} [Preorder ι]
  (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
  (f : ∀ i j, i ≤ j → X i → X j)

def of (i : ι) (x : X i) : Space X f :=
  @Quotient.mk' _ (directLimitSetoid X f) ⟨i, x⟩

theorem of_continuous (i : ι) : Continuous (of X f i) :=
  continuous_quotient_mk'.comp continuous_sigmaMk

theorem of_comp {i j : ι} (h : i ≤ j) (x : X i) :
    of X f j (f i j h x) = of X f i x := by
  apply @Quotient.sound' _ (directLimitSetoid X f)
  exact (Relation.EqvGen.rel _ _ ⟨i, j, h, x, rfl, rfl⟩).symm

end Maps

section UniversalProperty

variable {ι : Type*} [Preorder ι]
  (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
  (f : ∀ i j, i ≤ j → X i → X j)

noncomputable def lift {Y : Type*} [TopologicalSpace Y]
    (ψ : ∀ i, X i → Y)
    (hψ_comp : ∀ i j (h : i ≤ j) (x : X i), ψ j (f i j h x) = ψ i x) :
    Space X f → Y :=
  @Quotient.lift _ _ (directLimitSetoid X f) (fun σ => ψ σ.1 σ.2) <| by
    intro a b hab
    change ψ a.1 a.2 = ψ b.1 b.2
    induction hab with
    | rel a b hr =>
      obtain ⟨i, j, h, x, rfl, rfl⟩ := hr
      exact (hψ_comp i j h x).symm
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem lift_continuous {Y : Type*} [TopologicalSpace Y]
    (ψ : ∀ i, X i → Y)
    (hψ_cont : ∀ i, Continuous (ψ i))
    (hψ_comp : ∀ i j (h : i ≤ j) (x : X i), ψ j (f i j h x) = ψ i x) :
    Continuous (lift X f ψ hψ_comp) := by
  unfold lift
  exact (continuous_sigma fun i => hψ_cont i).quotient_lift _

end UniversalProperty

end TopologicalSpace.DirectLimit
