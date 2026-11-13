/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Atlas.TheoryOfComputation.code.LogSpace
import Atlas.TheoryOfComputation.code.HierarchyTheorems
import Atlas.TheoryOfComputation.code.SpaceComplexity
open SpaceComplexity LogSpace TuringMachine

namespace NLStrictPSPACE

/-- For every `m ≥ 10`, `m³ < 2^m`. Used to dominate `c · (log₂ n)²` by `n` asymptotically. -/
theorem two_pow_gt_cube (m : ℕ) (hm : 10 ≤ m) : m ^ 3 < 2 ^ m := by
  induction m with
  | zero => omega
  | succ n ih =>
    by_cases hn : 10 ≤ n
    · have ih' := ih hn
      have h1 : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      rw [h1, h2]
      have h3 : 3 * n ^ 2 + 3 * n + 1 ≤ n ^ 3 := by nlinarith
      linarith
    · interval_cases n <;> omega

/-- `(log₂ n)² = o(n)`: the function `n ↦ (Nat.log 2 n)²` is asymptotically dominated by `n`.
This is the key gap used to separate `NL` from `PSPACE`. -/
theorem log_sq_little_o_id :
    IsAsympDominated (fun n => (Nat.log 2 n) ^ 2) (fun n => n) := by
  intro c hc
  use 2 ^ (max 10 (c + 1))
  intro n hn
  have hn_pos : 0 < n := by
    calc (0 : ℕ) < 2 ^ max 10 (c + 1) := by positivity
      _ ≤ n := hn
  have hn_ne : n ≠ 0 := by omega
  set m := Nat.log 2 n with hm_def
  have h_pow_le : 2 ^ m ≤ n := Nat.pow_log_le_self 2 hn_ne
  have h_m_ge : max 10 (c + 1) ≤ m := by
    rw [hm_def]
    calc max 10 (c + 1)
        = Nat.log 2 (2 ^ max 10 (c + 1)) :=
          (Nat.log_pow (by norm_num : (1 : ℕ) < 2) _).symm
      _ ≤ Nat.log 2 n := Nat.log_mono_right hn
  have h_m_ge_10 : 10 ≤ m := le_trans (le_max_left 10 (c + 1)) h_m_ge
  have h_c_lt_m : c < m := by omega
  have h1 : c * m ^ 2 < m ^ 3 := by
    calc c * m ^ 2 < m * m ^ 2 :=
          Nat.mul_lt_mul_of_pos_right h_c_lt_m (by positivity)
      _ = m ^ 3 := by ring
  have h2 : m ^ 3 < 2 ^ m := two_pow_gt_cube m h_m_ge_10

  show c * (Nat.log 2 n) ^ 2 < n
  rw [← hm_def]
  linarith

/-- If `g = O(h)` and `h = o(f)`, then `g = o(f)`: composing a Big-O bound with a little-o
bound yields a little-o bound. -/
theorem isAsympBoundedBy_trans_isAsympDominated {g h f : ℕ → ℕ}
    (hgh : IsAsympBoundedBy g h) (hhf : IsAsympDominated h f) :
    IsAsympDominated g f := by
  intro c hc
  obtain ⟨C, n₁, hC, hg⟩ := hgh
  obtain ⟨n₂, hh⟩ := hhf (c * C) (Nat.mul_pos hc hC)
  use max n₁ n₂
  intro n hn
  have hn₁ : n₁ ≤ n := le_of_max_le_left hn
  have hn₂ : n₂ ≤ n := le_of_max_le_right hn
  have hstep1 : c * g n ≤ c * (C * h n) := Nat.mul_le_mul_left c (hg n hn₁)
  have hstep2 : c * (C * h n) = c * C * h n := by ring
  have hstep3 : c * C * h n < f n := hh n hn₂
  linarith

/-- Trivial pointwise bound: `(log₂ n)² ≤ n²` for all `n`. -/
theorem log_sq_le_sq (n : ℕ) : (Nat.log 2 n) ^ 2 ≤ n ^ 2 :=
  Nat.pow_le_pow_left (Nat.log_le_self 2 n) 2

/-- `SPACE((log₂ n)²) ⊆ PSPACE`: any language decidable in space `(log₂ n)²` is decidable
in polynomial space (in particular, in space `n²`). -/
theorem space_log_sq_subset_pspace {Γ : Type} (A : Set (List Γ))
    (hA : InSPACE (fun n => (Nat.log 2 n) ^ 2) A) : InPSPACE A := by
  obtain ⟨Q, _, hQ, M, hL, g, ⟨C, n₀, hC, hg⟩, hM⟩ := hA
  refine ⟨2, Q, inferInstance, hQ, M, hL, g, ⟨C, n₀, hC, fun n hn => ?_⟩, hM⟩
  calc g n ≤ C * (Nat.log 2 n) ^ 2 := hg n hn
    _ ≤ C * n ^ 2 := Nat.mul_le_mul_left C (log_sq_le_sq n)

/-- `(log₂ n)² = o(n + 2)`. Combined with the Space Hierarchy Theorem at bound `n + 2`,
this lets us separate `SPACE(n + 2)` from `NL ⊆ SPACE(log² n)`. -/
theorem log_sq_little_o_succ2 :
    IsAsympDominated (fun n => (Nat.log 2 n) ^ 2) (fun n => n + 2) := by
  intro c hc
  obtain ⟨n₀, hn₀⟩ := log_sq_little_o_id c hc
  use n₀
  intro n hn
  have h := hn₀ n hn
  linarith

/-- A language decidable in space `(log₂ n)²` is decidable in space `o(n + 2)`, i.e. it lies
in `SPACEo (n + 2)`. -/
theorem space_log_sq_in_spaceo_succ2 {Γ : Type} (A : Set (List Γ))
    (hA : InSPACE (fun n => (Nat.log 2 n) ^ 2) A) : InSPACEo (fun n => n + 2) A := by
  obtain ⟨Q, _, hQ, M, hL, g, hglog, hM⟩ := hA
  exact ⟨Q, inferInstance, hQ, M, hL, g,
    isAsympBoundedBy_trans_isAsympDominated hglog log_sq_little_o_succ2, hM⟩

/-- `SPACE(n + 2) ⊆ PSPACE`. Linear space is contained in polynomial space (in particular `n²`).
-/
theorem space_succ2_subset_pspace {Γ : Type} (A : Set (List Γ))
    (hA : InSPACE (fun n => n + 2) A) : InPSPACE A := by
  obtain ⟨Q, _, hQ, M, hL, g, ⟨C, n₀, hC, hg⟩, hM⟩ := hA
  refine ⟨2, Q, inferInstance, hQ, M, hL, g, ⟨C, max n₀ 3, hC, fun n hn => ?_⟩, hM⟩
  have hn₀ : n₀ ≤ n := le_of_max_le_left hn
  have hn3 : 3 ≤ n := le_of_max_le_right hn
  have h_bound : n + 2 ≤ n ^ 2 := by nlinarith
  calc g n ≤ C * (n + 2) := hg n hn₀
    _ ≤ C * n ^ 2 := Nat.mul_le_mul_left C h_bound

end NLStrictPSPACE
