/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Sequences

open Filter

/-- For a bounded real sequence `x : ℕ → ℝ`, the filter-theoretic `limsup` along
`atTop` agrees with the textbook definition
`limsup x = inf_{n} sup_{k ≥ n} x k`, here written as
`⨅ n, ⨆ i, x (i + n)`.

This realizes the informal definition: for bounded `{xₙ}`,
`limsup xₙ := lim_{n→∞} sup{xₖ : k ≥ n}`. -/
theorem limsup_eq_lim_sup_tail (x : ℕ → ℝ) (hb : BddAbove (Set.range x))
    (hb' : BddBelow (Set.range x)) :
    Filter.limsup x Filter.atTop = ⨅ n : ℕ, ⨆ i : ℕ, x (i + n) := by
  have hbdd : IsBoundedUnder (· ≤ ·) atTop x := hb.isBoundedUnder_of_range
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop x := by
    rw [IsCoboundedUnder, IsCobounded]
    obtain ⟨c, hc⟩ := hb'
    exact ⟨c, fun a ha => by
      rw [eventually_map, eventually_atTop] at ha
      obtain ⟨N, hN⟩ := ha
      exact le_trans (hc (Set.mem_range_self N)) (hN N le_rfl)⟩
  have hbdd_tail : ∀ n, BddAbove (Set.range (fun i => x (i + n))) := by
    intro n
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, by intro y ⟨i, hi⟩; rw [← hi]; exact hM (Set.mem_range_self (i + n))⟩
  have hbdd_below_sups : BddBelow (Set.range (fun n => ⨆ i : ℕ, x (i + n))) := by
    obtain ⟨c, hc⟩ := hb'
    exact ⟨c, by
      intro y ⟨n, hn⟩; rw [← hn]
      exact le_trans (hc (Set.mem_range_self (0 + n))) (le_ciSup (hbdd_tail n) 0)⟩
  apply le_antisymm
  ·
    apply le_ciInf
    intro n
    apply limsup_le_of_le hcobdd
    rw [eventually_atTop]
    refine ⟨n, fun m hm => ?_⟩
    calc x m = x ((m - n) + n) := by congr 1; omega
      _ ≤ ⨆ i, x (i + n) := le_ciSup (hbdd_tail n) (m - n)
  ·
    apply le_limsup_of_le hbdd
    intro b hb_ev
    rw [eventually_atTop] at hb_ev
    obtain ⟨N, hN⟩ := hb_ev
    calc ⨅ n, ⨆ i, x (i + n)
      ≤ ⨆ i, x (i + N) := ciInf_le hbdd_below_sups N
      _ ≤ b := ciSup_le (fun i => hN (i + N) (Nat.le_add_left N i))

/-- A bounded real sequence `x : ℕ → ℝ` converges to some limit `L` if and only
if its `limsup` and `liminf` (along `atTop`) coincide.

This is the standard characterization: a bounded sequence `{xₙ}` converges iff
`liminf xₙ = limsup xₙ`. -/
theorem convergent_iff_limsup_eq_liminf (x : ℕ → ℝ)
    (hbdd : BddAbove (Set.range x) ∧ BddBelow (Set.range x)) :
    (∃ L, Filter.Tendsto x Filter.atTop (nhds L)) ↔
    Filter.limsup x Filter.atTop = Filter.liminf x Filter.atTop := by
  constructor
  ·
    rintro ⟨L, hL⟩
    have h1 := hL.limsup_eq
    have h2 := hL.liminf_eq
    linarith
  ·
    intro heq
    exact ⟨Filter.limsup x Filter.atTop,
      tendsto_of_liminf_eq_limsup heq.symm rfl
        (hbdd.1.isBoundedUnder_of_range)
        (hbdd.2.isBoundedUnder_of_range)⟩

end Sequences
