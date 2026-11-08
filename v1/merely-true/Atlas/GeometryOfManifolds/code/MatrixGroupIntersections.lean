/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix

namespace CompatibleTriple

variable (l : Type*) [DecidableEq l] [Fintype l]

/-- The symplectic group $\mathrm{Sp}(2n) = \{A : A^T J A = J\}$, realized as a set of
real $(l \sqcup l) \times (l \sqcup l)$ matrices using the standard symplectic form $J$. -/
def Sp2n : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  { A | A.transpose * J l ℝ * A = J l ℝ }

/-- The orthogonal group $O(2n) = \{A : A^T A = I\}$. -/
def O2n : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  { A | A.transpose * A = 1 }

/-- The subgroup of $\mathrm{GL}(2n, \mathbb{R})$ that commutes with $J$, identified with
$\mathrm{GL}(n, \mathbb{C}) = \{A : AJ = JA\}$ via the standard complex structure $J$. -/
def GLnC : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  { A | A * J l ℝ = J l ℝ * A }

/-- The unitary group $U(n) = \mathrm{GL}(n, \mathbb{C}) \cap O(2n)$. -/
def Un : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  GLnC l ∩ O2n l

variable {l}

/-- Left-cancellation by the invertible matrix $J$: if $J M = J N$ then $M = N$. -/
lemma J_mul_left_cancel {M N : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (h : J l ℝ * M = J l ℝ * N) : M = N := by
  have hJinv : (J l ℝ)⁻¹ * (J l ℝ) = 1 := nonsing_inv_mul _ (isUnit_det_J l ℝ)
  calc M = ((J l ℝ)⁻¹ * J l ℝ) * M := by rw [hJinv, one_mul]
    _ = (J l ℝ)⁻¹ * (J l ℝ * N) := by rw [mul_assoc, ← h, ← mul_assoc]
    _ = N := by rw [← mul_assoc, hJinv, one_mul]

/-- If $A$ commutes with $J$ (i.e. $A \in \mathrm{GL}(n, \mathbb{C})$), so does $A^T$, using
that $J^T = -J$. -/
lemma comm_J_transpose {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (h : A * J l ℝ = J l ℝ * A) : A.transpose * J l ℝ = J l ℝ * A.transpose := by
  have h1 : (A * J l ℝ).transpose = (J l ℝ * A).transpose := by rw [h]
  simp [transpose_mul] at h1
  exact neg_injective h1.symm

/-- $\mathrm{Sp}(2n) \cap \mathrm{GL}(n, \mathbb{C}) \subseteq O(2n)$: a symplectic matrix
which is also complex-linear is orthogonal. -/
lemma sp_cap_gl_sub_O {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hSp : A ∈ Sp2n l) (hGL : A ∈ GLnC l) : A ∈ O2n l := by
  simp only [Sp2n, GLnC, O2n, Set.mem_setOf_eq] at *
  apply J_mul_left_cancel
  rw [mul_one]
  have hcomm_t := comm_J_transpose hGL
  calc J l ℝ * (A.transpose * A)
      = (J l ℝ * A.transpose) * A := by rw [mul_assoc]
    _ = (A.transpose * J l ℝ) * A := by rw [hcomm_t]
    _ = A.transpose * J l ℝ * A := by rw [mul_assoc]
    _ = J l ℝ := hSp

/-- $O(2n) \cap \mathrm{GL}(n, \mathbb{C}) \subseteq \mathrm{Sp}(2n)$: an orthogonal matrix
which is also complex-linear is symplectic. -/
lemma O_cap_gl_sub_Sp {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hO : A ∈ O2n l) (hGL : A ∈ GLnC l) : A ∈ Sp2n l := by
  simp only [Sp2n, GLnC, O2n, Set.mem_setOf_eq] at *
  calc A.transpose * J l ℝ * A
      = A.transpose * (J l ℝ * A) := by rw [mul_assoc]
    _ = A.transpose * (A * J l ℝ) := by rw [hGL]
    _ = (A.transpose * A) * J l ℝ := by rw [mul_assoc]
    _ = 1 * J l ℝ := by rw [hO]
    _ = J l ℝ := by rw [one_mul]

/-- $\mathrm{Sp}(2n) \cap O(2n) \subseteq \mathrm{GL}(n, \mathbb{C})$: a symplectic and
orthogonal matrix is automatically complex-linear. -/
lemma sp_cap_O_sub_GL {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hSp : A ∈ Sp2n l) (hO : A ∈ O2n l) : A ∈ GLnC l := by
  simp only [Sp2n, GLnC, O2n, Set.mem_setOf_eq] at *
  have hO' : A * A.transpose = 1 := mul_eq_one_comm.mp hO
  have h : A * (A.transpose * J l ℝ * A) = J l ℝ * A := by
    calc A * (A.transpose * J l ℝ * A)
        = A * A.transpose * J l ℝ * A := by simp [Matrix.mul_assoc]
      _ = 1 * J l ℝ * A := by rw [hO']
      _ = J l ℝ * A := by rw [one_mul]
  rw [hSp] at h
  exact h


/-- **The "two out of three" theorem for compatible triples.**
$$\mathrm{Sp}(2n) \cap O(2n) = \mathrm{Sp}(2n) \cap \mathrm{GL}(n, \mathbb{C})
= O(2n) \cap \mathrm{GL}(n, \mathbb{C}) = U(n).$$
This file proves the first equality; the others follow by the same argument. -/
theorem sp_cap_O_eq_U : Sp2n l ∩ O2n l = Un l := by
  ext A
  simp only [Set.mem_inter_iff, Un]
  constructor
  · intro ⟨hSp, hO⟩
    exact ⟨sp_cap_O_sub_GL hSp hO, hO⟩
  · intro ⟨hGL, hO⟩
    exact ⟨O_cap_gl_sub_Sp hO hGL, hO⟩

end CompatibleTriple
