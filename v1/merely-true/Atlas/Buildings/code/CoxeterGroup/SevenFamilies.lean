/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Atlas.Buildings.code.CoxeterGroup.TypeACoxeterSystem
import Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
import Atlas.Buildings.code.CoxeterGroup.SignedPermGroup
import Atlas.Buildings.code.CoxeterGroup.TypeCInjectivityHelper

namespace CoxeterMatrix

/-- The Coxeter matrix of type $A_{n-1}$ (linear Dynkin diagram with $n$ nodes). -/
abbrev typeA (n : ℕ) : CoxeterMatrix (Fin n) := CoxeterMatrix.A n

/-- The Coxeter matrix of type $C_n$ (also denoted $B_n$ in Mathlib): hyperoctahedral group. -/
abbrev typeC (n : ℕ) : CoxeterMatrix (Fin n) := CoxeterMatrix.B n

/-- The Coxeter matrix of type $D_n$ (fork at one end). -/
abbrev typeD (n : ℕ) : CoxeterMatrix (Fin n) := CoxeterMatrix.D n

/-- Explicit formula for the type-$A$ Coxeter matrix entries: $1$ on the diagonal,
$3$ on the off-diagonal at adjacent indices, $2$ otherwise. -/
theorem typeA_matrix_formula (n : ℕ) (i j : Fin n) :
    typeA n i j =
      if i = j then 1
      else if (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ) then 3
      else 2 := by
  simp [typeA, CoxeterMatrix.A, Matrix.of_apply]

/-- The affine type-$\tilde A_n$ Coxeter matrix: linear diagram on $n+1$ nodes wrapped into a cycle. -/
def typeAffinA (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
    else if (i.val + 1) % (n + 1) = j.val ∨ (j.val + 1) % (n + 1) = i.val then
      if n ≤ 1 then 0
      else 3
    else 2
  isSymm := by
    ext i j; simp only [Matrix.of_apply, Matrix.transpose_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : ¬(j = i) := fun h => hij h.symm
      simp only [hij, hji, ite_false]
      congr 1
      exact propext ⟨fun h => h.symm, fun h => h.symm⟩
  diagonal := by intro i; simp [Matrix.of_apply]
  off_diagonal := by
    intro i j hij; simp only [Matrix.of_apply, hij, ite_false]
    split_ifs <;> omega





end CoxeterMatrix

/-- Adjacency predicate encoding the edges of the affine type-$\tilde B_n$ Dynkin diagram. -/
def affinBCond (i j : ℕ) : Prop :=
  (i = 0 ∧ j = 2) ∨ (j = 0 ∧ i = 2) ∨
  (i = 1 ∧ j = 2) ∨ (j = 1 ∧ i = 2) ∨
  (i + 1 = j ∧ i ≥ 2) ∨ (j + 1 = i ∧ j ≥ 2)

/-- The affine-$B$ adjacency predicate is decidable. -/
instance (i j : ℕ) : Decidable (affinBCond i j) := by unfold affinBCond; infer_instance

/-- The affine-$B$ adjacency predicate is symmetric in its arguments. -/
lemma affinBCond_comm (i j : ℕ) : affinBCond i j ↔ affinBCond j i := by
  unfold affinBCond
  constructor <;> intro h <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  all_goals first
    | (right; left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (right; right; right; left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (right; right; left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (right; right; right; right; right; exact ⟨h1, h2⟩)
    | (right; right; right; right; left; exact ⟨h1, h2⟩)

/-- Adjacency predicate encoding the edges of the affine type-$\tilde D_n$ Dynkin diagram. -/
def affinDCond (n i j : ℕ) : Prop :=
  (i = 0 ∧ j = 2) ∨ (j = 0 ∧ i = 2) ∨
  (i = 1 ∧ j = 2) ∨ (j = 1 ∧ i = 2) ∨
  (i + 1 = j ∧ i ≥ 2 ∧ j + 2 ≤ n) ∨ (j + 1 = i ∧ j ≥ 2 ∧ i + 2 ≤ n) ∨
  (i + 2 = n ∧ j = n - 1) ∨ (j + 2 = n ∧ i = n - 1) ∨
  (i + 2 = n ∧ j = n) ∨ (j + 2 = n ∧ i = n)

/-- The affine-$D$ adjacency predicate is decidable. -/
instance (n i j : ℕ) : Decidable (affinDCond n i j) := by unfold affinDCond; infer_instance

/-- The affine-$D$ adjacency predicate is symmetric in $i$ and $j$. -/
lemma affinDCond_comm (n i j : ℕ) : affinDCond n i j ↔ affinDCond n j i := by
  unfold affinDCond
  constructor <;> intro h <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                  ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  all_goals first
    | (right; left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (right; right; right; left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (right; right; left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (right; right; right; right; right; left; exact ⟨h1, h2, h3⟩)
    | (right; right; right; right; left; exact ⟨h1, h2, h3⟩)
    | (right; right; right; right; right; right; right; left; constructor <;> omega)
    | (right; right; right; right; right; right; left; constructor <;> omega)
    | (right; right; right; right; right; right; right; right; right; constructor <;> omega)
    | (right; right; right; right; right; right; right; right; left; constructor <;> omega)

namespace CoxeterMatrix

/-- The affine type-$\tilde B_n$ Coxeter matrix. -/
def typeAffinB (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
    else if affinBCond i.val j.val then
      if max i.val j.val = n then 4 else 3
    else 2
  isSymm := by
    ext i j; simp only [Matrix.of_apply, Matrix.transpose_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : ¬(j = i) := fun h => hij h.symm
      simp only [hij, hji, ite_false]
      simp only [affinBCond_comm, max_comm]
  diagonal := by intro i; simp [Matrix.of_apply]
  off_diagonal := by
    intro i j hij; simp only [Matrix.of_apply, hij, ite_false]
    split_ifs <;> omega

/-- The affine type-$\tilde C_n$ Coxeter matrix. -/
def typeAffinC (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then
      if min i.val j.val = 0 ∨ max i.val j.val = n then 4
      else 3
    else 2
  isSymm := by
    ext i j; simp only [Matrix.of_apply, Matrix.transpose_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : ¬(j = i) := fun h => hij h.symm
      simp only [hij, hji, ite_false]
      have adj_symm : (i.val + 1 = j.val ∨ j.val + 1 = i.val) ↔
                       (j.val + 1 = i.val ∨ i.val + 1 = j.val) :=
        ⟨fun h => h.symm, fun h => h.symm⟩
      have minmax_symm : (min i.val j.val = 0 ∨ max i.val j.val = n) ↔
                          (min j.val i.val = 0 ∨ max j.val i.val = n) := by
        rw [min_comm, max_comm]
      split_ifs with h1 h2 h3 h4 h5 h6
      all_goals first | rfl | (exfalso; simp_all)
  diagonal := by intro i; simp [Matrix.of_apply]
  off_diagonal := by
    intro i j hij; simp only [Matrix.of_apply, hij, ite_false]
    split_ifs <;> omega

/-- The affine type-$\tilde D_n$ Coxeter matrix. -/
def typeAffinD (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
    else if affinDCond n i.val j.val then 3
    else 2
  isSymm := by
    ext i j; simp only [Matrix.of_apply, Matrix.transpose_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : ¬(j = i) := fun h => hij h.symm
      simp only [hij, hji, ite_false]
      simp only [affinDCond_comm]
  diagonal := by intro i; simp [Matrix.of_apply]
  off_diagonal := by
    intro i j hij; simp only [Matrix.of_apply, hij, ite_false]
    split_ifs <;> omega

end CoxeterMatrix
