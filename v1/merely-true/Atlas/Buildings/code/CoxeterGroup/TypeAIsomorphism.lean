/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.PresentedGroup
import Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper

open Equiv Equiv.Perm Function Set

namespace SymmetricCoxeter

/-- The adjacent transposition $\alpha_i = (i, i+1) \in S_{n+1}$. -/
def adjTransposition (n : ℕ) (i : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap (Fin.castSucc i) (Fin.succ i)

/-- Two swaps sharing a common first index multiply to a $3$-cycle, hence $(\sigma\tau)^3 = 1$. -/
theorem swap_mul_swap_common_first_pow_three {α : Type*} [Fintype α] [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (Equiv.swap a b * Equiv.swap a c) ^ 3 = 1 := by
  rw [← (isThreeCycle_swap_mul_swap_same hab hac hbc).orderOf]
  exact pow_orderOf_eq_one _

/-- Adjacent swaps (sharing the middle element) satisfy $(\operatorname{swap}(a,b) \operatorname{swap}(b,c))^3 = 1$. -/
theorem swap_mul_swap_adjacent_pow_three {α : Type*} [Fintype α] [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (Equiv.swap a b * Equiv.swap b c) ^ 3 = 1 := by
  rw [Equiv.swap_comm a b]
  exact swap_mul_swap_common_first_pow_three hab.symm hbc hac

/-- If $i+1 = j$ as naturals then $\operatorname{succ}(i) = \operatorname{castSucc}(j)$ in $\operatorname{Fin}(n+1)$. -/
theorem succ_eq_castSucc_of_val_succ {n : ℕ} {i j : Fin n} (h : (i : ℕ) + 1 = (j : ℕ)) :
    Fin.succ i = Fin.castSucc j := by
  ext; simp [Fin.val_succ, Fin.val_castSucc]; omega

/-- Adjacent transpositions satisfy the Coxeter relation $(\alpha_i \alpha_j)^{m_{ij}} = 1$
for the type-$A$ Coxeter matrix. -/
theorem adjTransposition_coxeter_rel (n : ℕ) (i j : Fin n) :
    (adjTransposition n i * adjTransposition n j) ^ (CoxeterMatrix.A n i j) = 1 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  split_ifs with hij hadj
  ·
    subst hij; simp [adjTransposition, swap_mul_self]
  ·
    rcases hadj with h | h
    ·

      have hkey : Fin.succ j = Fin.castSucc i := succ_eq_castSucc_of_val_succ h
      unfold adjTransposition; rw [← hkey]
      rw [Equiv.swap_comm (Fin.castSucc j) (Fin.succ j)]
      exact swap_mul_swap_common_first_pow_three
        (by intro heq; simp [Fin.ext_iff] at heq; omega)
        (by intro heq; simp [Fin.ext_iff] at heq)
        (by intro heq; simp [Fin.ext_iff] at heq; omega)
    ·

      have hkey : Fin.succ i = Fin.castSucc j := succ_eq_castSucc_of_val_succ h
      unfold adjTransposition; rw [hkey]
      exact swap_mul_swap_adjacent_pow_three
        (by intro heq; exact hij (Fin.castSucc_injective _ heq))
        (by intro h; simp [Fin.ext_iff] at h)
        (by intro heq; simp [Fin.ext_iff] at heq; omega)
  ·

    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    have nodup : [Fin.castSucc i, Fin.succ i, Fin.castSucc j, Fin.succ j].Nodup := by
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
        List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        push Not
        refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> simp [Fin.ext_iff] at heq <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        push Not
        constructor <;> intro heq <;> simp [Fin.ext_iff] at heq <;> omega
      · simp only [List.mem_singleton]
        intro heq; simp [Fin.ext_iff] at heq

    show (Equiv.swap _ _ * Equiv.swap _ _) ^ 2 = 1
    rw [(disjoint_swap_swap nodup).commute.mul_pow]
    simp [sq, Equiv.swap_mul_self]

/-- The free-group lift of `adjTransposition` sends every type-$A$ relation to the identity. -/
theorem adjTransposition_lift_rels (n : ℕ) :
    ∀ r ∈ (CoxeterMatrix.A n).relationsSet, FreeGroup.lift (adjTransposition n) r = 1 := by
  intro r hr
  obtain ⟨⟨i, j⟩, rfl⟩ := hr
  simp only [CoxeterMatrix.relation, uncurry, map_pow, map_mul, FreeGroup.lift_apply_of]
  exact adjTransposition_coxeter_rel n i j

/-- Canonical homomorphism $W(A_{n-1}) \to S_{n+1}$ from the type-$A$ Coxeter group to the
symmetric group, sending generators to adjacent transpositions. -/
noncomputable def coxeterToPermHom (n : ℕ) :
    (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin (n + 1)) :=
  PresentedGroup.toGroup (adjTransposition_lift_rels n)

/-- `coxeterToPermHom` sends the $i$-th simple generator to the $i$-th adjacent transposition. -/
theorem coxeterToPermHom_generator (n : ℕ) (i : Fin n) :
    coxeterToPermHom n (CoxeterMatrix.simple (CoxeterMatrix.A n) i) = adjTransposition n i :=
  PresentedGroup.toGroup.of _

/-- `coxeterToPermHom` is surjective: adjacent transpositions generate $S_{n+1}$. -/
theorem coxeterToPermHom_surjective (n : ℕ) :
    Function.Surjective (coxeterToPermHom n) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  have hgen : ∀ i : Fin n, adjTransposition n i ∈ (coxeterToPermHom n).range :=
    fun i => ⟨_, coxeterToPermHom_generator n i⟩
  intro σ _
  have hmcl := Equiv.Perm.mclosure_swap_castSucc_succ n
  have hσ : σ ∈ Submonoid.closure
      (Set.range fun i : Fin n => Equiv.swap (Fin.castSucc i) (Fin.succ i)) := by
    rw [hmcl]; exact Submonoid.mem_top σ
  have hle : Submonoid.closure
      (Set.range fun i : Fin n => Equiv.swap (Fin.castSucc i) (Fin.succ i)) ≤
      (coxeterToPermHom n).range.toSubmonoid := by
    exact Submonoid.closure_le.mpr (fun x ⟨i, hi⟩ => hi ▸ hgen i)
  exact hle hσ





end SymmetricCoxeter
