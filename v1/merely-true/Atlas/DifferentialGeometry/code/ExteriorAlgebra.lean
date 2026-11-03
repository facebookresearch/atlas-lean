/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Ring.CharZero
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Basic

open Matrix Finset Module

set_option autoImplicit false

namespace ExteriorAlgebra

variable {R : Type*} [CommRing R] {n : ℕ}

def wedge (v w : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => v i * w j - w i * v j

@[simp]
theorem wedge_apply (v w : Fin n → R) (i j : Fin n) :
    wedge v w i j = v i * w j - w i * v j := rfl

theorem wedge_transpose (v w : Fin n → R) :
    (wedge v w)ᵀ = -(wedge v w) := by
  ext i j; simp only [transpose_apply, wedge_apply, neg_apply]; ring

def antisymmMatrices (n : ℕ) (R : Type*) [CommRing R] :
    Submodule R (Matrix (Fin n) (Fin n) R) where
  carrier := {M | Mᵀ = -M}
  add_mem' {a b} (ha : aᵀ = -a) (hb : bᵀ = -b) := by
    show (a + b)ᵀ = -(a + b)
    rw [transpose_add, ha, hb, neg_add]
  zero_mem' := by simp
  smul_mem' r a (ha : aᵀ = -a) := by
    show (r • a)ᵀ = -(r • a)
    rw [transpose_smul, ha, smul_neg]

theorem wedge_mem_antisymm (v w : Fin n → R) :
    wedge v w ∈ antisymmMatrices n R :=
  wedge_transpose v w

abbrev StrictUpperTriIdx (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

set_option maxHeartbeats 400000 in
theorem wedge_stdBasis_upper [DecidableEq (Fin n)] (p q : StrictUpperTriIdx n) :
    wedge (Pi.single p.1.1 (1 : R)) (Pi.single p.1.2 (1 : R)) q.1.1 q.1.2 =
    if p = q then 1 else 0 := by
  simp only [wedge_apply, Pi.single_apply]
  have hp := p.2; have hpne : p.1.1 ≠ p.1.2 := Fin.ne_of_lt hp
  by_cases h : p = q
  · subst h; simp [hpne, hpne.symm]
  · simp only [h, ite_false]
    suffices h1 : ¬(q.1.1 = p.1.2 ∧ q.1.2 = p.1.1) by
      suffices h2 : ¬(q.1.2 = p.1.1 ∧ q.1.1 = p.1.2) by
        by_cases hA : q.1.1 = p.1.1 <;> by_cases hB : q.1.2 = p.1.2 <;>
          by_cases hC : q.1.1 = p.1.2 <;> by_cases hD : q.1.2 = p.1.1 <;>
          simp_all [Subtype.ext_iff, Prod.ext_iff]
      exact fun ⟨ha, hb⟩ => h1 ⟨hb, ha⟩
    exact fun ⟨ha, hb⟩ => not_lt.mpr (le_of_lt hp) (ha ▸ hb ▸ q.2)

end ExteriorAlgebra



namespace ExteriorSquare

variable {R : Type*} [CommRing R] {n : ℕ}

abbrev Idx (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def matrix (L : Matrix (Fin n) (Fin n) R) : Matrix (Idx n) (Idx n) R :=
  fun p q => L p.1.1 q.1.1 * L p.1.2 q.1.2 - L p.1.1 q.1.2 * L p.1.2 q.1.1

lemma sum_sum_eq_two_sum_lt (f : Fin n → Fin n → R)
    (hdiag : ∀ i, f i i = 0) (hsymm : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = 2 * ∑ p : Idx n, f p.1.1 p.1.2 := by
  have hfilt_conv : ∑ p : Idx n, f p.1.1 p.1.2 =
    ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), f p.1 p.2 := by
    rw [show (Finset.univ : Finset (Idx n)) =
      (Finset.univ : Finset (Fin n × Fin n)).subtype (fun p => p.1 < p.2) from by
        ext ⟨x, hx⟩; simp]
    exact @Finset.sum_subtype_eq_sum_filter _ _ (Finset.univ : Finset (Fin n × Fin n)) _
      (fun x => f x.1 x.2) (fun p => p.1 < p.2) _
  rw [hfilt_conv, (Fintype.sum_prod_type (f := fun p : Fin n × Fin n => f p.1 p.2)).symm]
  have key := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n × Fin n))
    (fun p : Fin n × Fin n => p.1 < p.2) (fun p => f p.1 p.2)
  suffices hflip : ∑ p ∈ Finset.filter (fun p : Fin n × Fin n => ¬p.1 < p.2) Finset.univ,
      f p.1 p.2 =
    ∑ p ∈ Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ, f p.1 p.2 by
    linear_combination key.symm + hflip
  rw [show Finset.filter (fun p : Fin n × Fin n => ¬p.1 < p.2) Finset.univ =
    Finset.filter (fun p : Fin n × Fin n => p.2 ≤ p.1) Finset.univ from by
      ext ⟨a, b⟩; simp [not_lt]]
  have hle_split : Finset.filter (fun p : Fin n × Fin n => p.2 ≤ p.1) Finset.univ =
    Finset.filter (fun p : Fin n × Fin n => p.2 < p.1) Finset.univ ∪
    Finset.filter (fun p : Fin n × Fin n => p.2 = p.1) Finset.univ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact le_iff_lt_or_eq
  have hdisj : Disjoint (Finset.filter (fun p : Fin n × Fin n => p.2 < p.1) Finset.univ)
    (Finset.filter (fun p : Fin n × Fin n => p.2 = p.1) Finset.univ) := by
    apply Finset.disjoint_filter.mpr; intro ⟨a, b⟩ _ h1 h2; omega
  rw [show ∑ p ∈ Finset.filter (fun p : Fin n × Fin n => p.2 ≤ p.1) Finset.univ, f p.1 p.2 =
    (∑ p ∈ Finset.filter (fun p : Fin n × Fin n => p.2 < p.1) Finset.univ, f p.1 p.2) +
    (∑ p ∈ Finset.filter (fun p : Fin n × Fin n => p.2 = p.1) Finset.univ, f p.1 p.2) from by
      rw [← Finset.sum_union hdisj, hle_split]]
  rw [show ∑ p ∈ Finset.filter (fun p : Fin n × Fin n => p.2 = p.1) Finset.univ, f p.1 p.2 =
      0 from by
    apply Finset.sum_eq_zero; intro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h; rw [← h, hdiag]]
  rw [add_zero]
  apply Finset.sum_nbij (fun p : Fin n × Fin n => (p.2, p.1))
  · intro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; exact h
  · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
  · intro ⟨a, b⟩ h
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact ⟨(b, a), h, rfl⟩
  · intro ⟨a, b⟩ _; exact hsymm a b

set_option maxHeartbeats 800000 in
theorem trace_exteriorSquare (L : Matrix (Fin n) (Fin n) R) :
    2 * Matrix.trace (matrix L) = Matrix.trace L ^ 2 - Matrix.trace (L * L) := by
  simp only [Matrix.trace, Matrix.diag, matrix, Matrix.mul_apply]
  rw [sq, Fintype.sum_mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [sum_sum_eq_two_sum_lt]
  · intro i; ring
  · intro i j; ring




end ExteriorSquare


