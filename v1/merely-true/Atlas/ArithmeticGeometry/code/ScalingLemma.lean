/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring

noncomputable section

open ValuationSubring

/-- Scaling Lemma (Lemma 16.32). Given finitely many nonzero elements
$x_0, \ldots, x_n \in K$ of a field equipped with a valuation subring $A$,
there exists a nonzero scalar $\lambda \in K$ such that all $\lambda x_i$ lie
in $A$ and at least one $\lambda x_i$ is a unit of $A$. -/
theorem scaling_lemma {K : Type*} [Field K] (A : ValuationSubring K)
    (n : ℕ) (x : Fin (n + 1) → K) (hx : ∀ i, x i ≠ 0) :
    ∃ (l : K) (_ : l ≠ 0) (hmem : ∀ i, l * x i ∈ A),
      ∃ i, IsUnit (⟨l * x i, hmem i⟩ : A) := by
  induction n with
  | zero =>

    have hmem : ∀ i : Fin 1, (x 0)⁻¹ * x i ∈ A := fun i => by
      have : i = 0 := Fin.ext (Fin.val_eq_zero i)
      rw [this, inv_mul_cancel₀ (hx 0)]; exact A.one_mem
    refine ⟨(x 0)⁻¹, inv_ne_zero (hx 0), hmem, ⟨0, ?_⟩⟩
    have h1 : (x 0)⁻¹ * x 0 = 1 := inv_mul_cancel₀ (hx 0)
    have : (⟨(x 0)⁻¹ * x 0, hmem 0⟩ : A) = 1 := Subtype.ext h1
    rw [this]; exact isUnit_one
  | succ m ih =>

    have hx' : ∀ i : Fin (m + 1), (x ∘ Fin.castSucc) i ≠ 0 := fun i => hx _
    obtain ⟨l, hl, hmem_old, i₀, hunit_old⟩ := ih (x ∘ Fin.castSucc) hx'

    by_cases hlast : l * x (Fin.last (m + 1)) ∈ A
    ·
      have hmem : ∀ i : Fin (m + 2), l * x i ∈ A := fun i =>
        Fin.lastCases hlast (fun j => hmem_old j) i
      refine ⟨l, hl, hmem, ⟨Fin.castSucc i₀, ?_⟩⟩
      exact hunit_old
    ·
      have hinv : (l * x (Fin.last (m + 1)))⁻¹ ∈ A :=
        (A.mem_or_inv_mem (l * x (Fin.last (m + 1)))).resolve_left hlast
      set xlast := x (Fin.last (m + 1)) with xlast_def
      have hxlast_ne : xlast ≠ 0 := hx (Fin.last (m + 1))

      have hmem : ∀ i : Fin (m + 2), xlast⁻¹ * x i ∈ A := fun i => by
        refine Fin.lastCases ?_ (fun j => ?_) i
        ·
          rw [inv_mul_cancel₀ hxlast_ne]; exact A.one_mem
        ·
          have key : xlast⁻¹ * x (Fin.castSucc j) =
              (l * x (Fin.castSucc j)) * (l * xlast)⁻¹ := by field_simp
          rw [key]; exact A.mul_mem _ _ (hmem_old j) hinv
      refine ⟨xlast⁻¹, inv_ne_zero hxlast_ne, hmem, ⟨Fin.last (m + 1), ?_⟩⟩

      have h1 : xlast⁻¹ * xlast = 1 := inv_mul_cancel₀ hxlast_ne
      have : (⟨xlast⁻¹ * xlast, hmem (Fin.last (m + 1))⟩ : A) = 1 := Subtype.ext h1
      rw [this]; exact isUnit_one

end
