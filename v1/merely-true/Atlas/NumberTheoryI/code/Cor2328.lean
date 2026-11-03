/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Lem2326
import Atlas.NumberTheoryI.code.Lem2327

noncomputable section

universe u

namespace GroupCohomology

open CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

def corollary_23_28_homology_ind_H0_iso [DecidableEq G] [Fintype G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    groupHomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
    groupHomology A 0 :=
  homology_induced_H0_iso A

def corollary_23_28_cohomology_coind_H0_iso [Fintype G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    groupCohomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
    groupCohomology A 0 :=
  cohomology_coinduced_H0_iso A

theorem corollary_23_28_homology_ind_vanishing [DecidableEq G] [Fintype G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) (n : ℕ) :
    Limits.IsZero
      (groupHomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1)) :=
  homology_induced_vanishing A n

theorem corollary_23_28_cohomology_coind_vanishing [Fintype G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) (n : ℕ) :
    Limits.IsZero
      (groupCohomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1)) :=
  cohomology_coinduced_vanishing A n

def corollary_23_28_cohomology_ind_H0_iso [Fintype G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    groupCohomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
    groupCohomology A 0 := by
  classical
  exact (groupCohomology.functor k G 0).mapIso (lemma_23_27 A) ≪≫
    cohomology_coinduced_H0_iso A

def corollary_23_28_homology_coind_H0_iso [DecidableEq G] [Fintype G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    groupHomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
    groupHomology A 0 := by
  classical
  exact (groupHomology.functor k G 0).mapIso (lemma_23_27 A).symm ≪≫
    homology_induced_H0_iso A

theorem corollary_23_28_cohomology_ind_vanishing [Fintype G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) (n : ℕ) :
    Limits.IsZero
      (groupCohomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1)) := by
  classical
  exact (cohomology_coinduced_vanishing A n).of_iso
    ((groupCohomology.functor k G (n + 1)).mapIso (lemma_23_27 A))

theorem corollary_23_28_homology_coind_vanishing [DecidableEq G] [Fintype G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) (n : ℕ) :
    Limits.IsZero
      (groupHomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1)) := by
  classical
  exact (homology_induced_vanishing A n).of_iso
    ((groupHomology.functor k G (n + 1)).mapIso (lemma_23_27 A).symm)

theorem induced_coinduced_cohomology_vanishing [Fintype G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :

    Nonempty (groupHomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
              groupHomology A 0) ∧

    Nonempty (groupCohomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
              groupCohomology A 0) ∧

    Nonempty (groupHomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
              groupHomology A 0) ∧

    Nonempty (groupCohomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
              groupCohomology A 0) ∧

    (∀ n : ℕ, Limits.IsZero
      (groupHomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1))) ∧

    (∀ n : ℕ, Limits.IsZero
      (groupCohomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1))) ∧

    (∀ n : ℕ, Limits.IsZero
      (groupHomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1))) ∧

    (∀ n : ℕ, Limits.IsZero
      (groupCohomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1))) := by
  classical
  exact ⟨⟨corollary_23_28_homology_ind_H0_iso A⟩,
         ⟨corollary_23_28_cohomology_ind_H0_iso A⟩,
         ⟨corollary_23_28_homology_coind_H0_iso A⟩,
         ⟨corollary_23_28_cohomology_coind_H0_iso A⟩,
         corollary_23_28_homology_ind_vanishing A,
         corollary_23_28_cohomology_ind_vanishing A,
         corollary_23_28_homology_coind_vanishing A,
         corollary_23_28_cohomology_coind_vanishing A⟩

end GroupCohomology
