/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.GroupTheory.Perm.Basic

open Finset Nat

namespace SetSystems

/-- The image under a permutation `σ` of $\{0, 1, \ldots, k-1\}$: the first `k` elements
of $[n]$ in the order induced by `σ`. -/
def initialSegment {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin n => i.val < k)).image σ

/-- (LYM inequality, general form) For any antichain $F$ of subsets of a finite type
$\alpha$, $\sum_{A \in F} \binom{|\alpha|}{|A|}^{-1} \le 1$. -/
theorem lym_inequality_general {α : Type*} [Fintype α]
    {F : Finset (Finset α)}
    (hF : IsAntichain (· ⊆ ·) (F : Set (Finset α))) :
    ∑ A ∈ F, ((Fintype.card α).choose A.card : ℚ)⁻¹ ≤ 1 :=
  Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose hF

/-- (Theorem 1.2.3, LYM inequality) For an antichain $F \subseteq 2^{[n]}$,
$\sum_{A \in F} 1/\binom{n}{|A|} \le 1$. -/
theorem lym_inequality (n : ℕ) (F : Finset (Finset (Fin n)))
    (hF : IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n)))) :
    ∑ A ∈ F, (1 : ℚ) / (n.choose A.card) ≤ 1 := by
  simp only [one_div]
  have h := lym_inequality_general hF
  convert h using 2 with A
  simp [Fintype.card_fin]

/-- (Theorem 1.2.2, Sperner's Theorem) Every antichain of subsets of $[n]$ has size at
most $\binom{n}{\lfloor n/2 \rfloor}$. -/
theorem sperner_theorem (n : ℕ) (F : Finset (Finset (Fin n)))
    (hF : IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n)))) :
    F.card ≤ n.choose (n / 2) := by


  have hLYM : ∑ A ∈ F, ((n.choose A.card : ℚ))⁻¹ ≤ 1 := by
    have h := lym_inequality_general hF
    simp only [Fintype.card_fin] at h
    exact h


  have hpos : (0 : ℚ) < (n.choose (n / 2)) := by
    exact_mod_cast Nat.choose_pos (Nat.div_le_self n 2)
  have hstep : ∑ _A ∈ F, ((n.choose (n / 2) : ℚ))⁻¹ ≤ 1 := by
    calc ∑ _A ∈ F, ((n.choose (n / 2) : ℚ))⁻¹
        ≤ ∑ A ∈ F, ((n.choose A.card : ℚ))⁻¹ := by
          apply Finset.sum_le_sum
          intro A _hA
          have hAcard : A.card ≤ n := by
            simpa [Fintype.card_fin] using A.card_le_univ
          exact inv_anti₀
            (by exact_mod_cast Nat.choose_pos hAcard)
            (by exact_mod_cast Nat.choose_le_middle A.card n)
      _ ≤ 1 := hLYM

  rw [Finset.sum_const, nsmul_eq_mul] at hstep
  rw [mul_inv_le_iff₀' hpos] at hstep
  simp only [mul_one] at hstep
  exact_mod_cast hstep

end SetSystems
