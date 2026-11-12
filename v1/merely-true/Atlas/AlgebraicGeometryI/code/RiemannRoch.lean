/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CohomologyP1
import Mathlib.Tactic

set_option maxHeartbeats 400000

open CohomologyP1

namespace RiemannRoch

variable (k : Type) [Field k]


/-- Dimension of `H^0(ℙ¹, 𝒪(n))` over `k`, via the Čech computation. -/
noncomputable def dimH0 (n : ℤ) : ℕ :=
  Module.finrank k ↥(CechH0 k n)

/-- Dimension of `H^1(ℙ¹, 𝒪(n))` over `k`, via the Čech computation. -/
noncomputable def dimH1 (n : ℤ) : ℕ :=
  Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n))


/-- On `ℙ¹`, for `n ≥ 0`, `dim H^0(𝒪(n)) = n + 1`. -/
theorem dimH0_nonneg (m : ℕ) : dimH0 k ↑m = m + 1 :=
  finrank_H0_nonneg k m

/-- On `ℙ¹`, for `n < 0`, `dim H^0(𝒪(n)) = 0`. -/
theorem dimH0_neg (n : ℤ) (hn : n < 0) : dimH0 k n = 0 := by
  unfold dimH0
  rw [H0_vanishes_neg k n hn]
  exact finrank_bot k (ℤ →₀ k)

/-- On `ℙ¹`, for `n ≥ 0`, `dim H^1(𝒪(n)) = 0`. -/
theorem dimH1_nonneg (m : ℕ) : dimH1 k ↑m = 0 :=
  finrank_H1_nonneg k m

/-- On `ℙ¹`, for `n < 0`, `dim H^1(𝒪(n)) = -n - 1`. -/
theorem dimH1_neg (n : ℤ) (hn : n < 0) : dimH1 k n = (-n - 1).toNat :=
  finrank_H1_neg k n hn


/-- Serre duality on `ℙ¹`: `dim H^1(𝒪(n)) = dim H^0(𝒪(-2 - n))`. -/
theorem serre_duality_P1 (n : ℤ) : dimH1 k n = dimH0 k (-2 - n) := by
  by_cases hn : 0 ≤ n
  ·
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [dimH1_nonneg, dimH0_neg k (-2 - ↑m) (by omega)]
  · push Not at hn

    by_cases hn2 : n = -1
    ·
      subst hn2
      rw [dimH1_neg k (-1) (by norm_num)]
      simp
      rw [dimH0_neg k (-1) (by norm_num)]
    ·
      have hn_le : n ≤ -2 := by omega
      have h_nn : 0 ≤ -2 - n := by omega
      rw [dimH1_neg k n hn]

      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h_nn
      rw [hm, dimH0_nonneg]

      zify [show 0 ≤ -n - 1 by omega]
      rw [← hm]
      omega


/-- Riemann–Roch on `ℙ¹`: `dim H^0(𝒪(d)) - dim H^1(𝒪(d)) = d + 1`. -/
theorem riemann_roch_P1 (d : ℤ) :
    (dimH0 k d : ℤ) - (dimH1 k d : ℤ) = d + 1 := by
  by_cases hd : 0 ≤ d
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    rw [dimH0_nonneg, dimH1_nonneg]
    push_cast
    ring
  · push Not at hd
    rw [dimH0_neg k d hd, dimH1_neg k d hd]
    push_cast
    rw [Int.toNat_of_nonneg (show 0 ≤ -d - 1 by omega)]
    omega


/-- The canonical bundle on `ℙ¹` is `𝒪(-2)`; `dim H^0(K) = 0`. -/
theorem canonical_bundle_P1_H0 : dimH0 k (-2) = 0 :=
  dimH0_neg k (-2) (by norm_num)

/-- The canonical bundle on `ℙ¹`: `dim H^1(K) = 1`. -/
theorem canonical_bundle_P1_H1 : dimH1 k (-2) = 1 := by
  rw [dimH1_neg k (-2) (by norm_num)]
  norm_num


/-- Genus of a smooth plane curve of degree `d`: `(d - 1)(d - 2) / 2`. -/
def genus (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

/-- A line in `ℙ²` has genus 0. -/
theorem genus_line : genus 1 = 0 := by decide

/-- A smooth conic in `ℙ²` has genus 0. -/
theorem genus_conic : genus 2 = 0 := by decide

/-- A smooth plane cubic has genus 1 (an elliptic curve). -/
theorem genus_cubic : genus 3 = 1 := by decide

/-- A smooth plane quartic has genus 3. -/
theorem genus_quartic : genus 4 = 3 := by decide


/-- Adjunction formula for a smooth plane curve of degree `d`:
`d(d - 3) = 2g - 2`. -/
theorem adjunction_formula_nonneg (d : ℕ) :
    d * (d - 3) = 2 * genus d - 2 := by
  unfold genus
  by_cases hd : d ≤ 4
  · interval_cases d <;> simp
  · push Not at hd
    have h_even : 2 ∣ (d - 1) * (d - 2) := by
      rcases Nat.even_or_odd (d - 1) with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨k * (d - 2), by rw [hk]; ring⟩
      · have hd2 : d - 2 = 2 * k := by omega
        exact ⟨(d - 1) * k, by rw [hd2]; ring⟩
    rw [Nat.mul_div_cancel' h_even]
    have h_ge : 2 ≤ (d - 1) * (d - 2) :=
      Nat.le_trans (by norm_num : 2 ≤ 4 * 3) (Nat.mul_le_mul (by omega) (by omega))
    zify [show 3 ≤ d by omega, show 1 ≤ d by omega, show 2 ≤ d by omega, h_ge]
    ring

/-- Alternative form of the adjunction formula: `d(d - 3) + 2 = (d - 1)(d - 2)`. -/
theorem adjunction_formula_alt (d : ℕ) (hd : 3 ≤ d) :
    d * (d - 3) + 2 = (d - 1) * (d - 2) := by
  zify [hd, show 1 ≤ d by omega, show 2 ≤ d by omega]
  ring


/-- Euler characteristic of `𝒪(n)` on `ℙ¹`: `dim H^0 - dim H^1`. -/
noncomputable def euler_char (n : ℤ) : ℤ :=
  (dimH0 k n : ℤ) - (dimH1 k n : ℤ)

/-- Euler characteristic formula on `ℙ¹`: `χ(𝒪(n)) = n + 1`. -/
theorem euler_char_eq (n : ℤ) : euler_char k n = n + 1 :=
  riemann_roch_P1 k n

/-- Euler characteristic of the structure sheaf on `ℙ¹`: `χ(𝒪) = 1`. -/
theorem euler_char_structure_sheaf : euler_char k 0 = 1 := by
  rw [euler_char_eq]; ring

/-- Serre duality version of Riemann–Roch on `ℙ¹`:
`dim H^0(𝒪(d)) - dim H^0(𝒪(-2 - d)) = d + 1`. -/
theorem riemann_roch_serre_form (d : ℤ) :
    (dimH0 k d : ℤ) - (dimH0 k (-2 - d) : ℤ) = d + 1 := by
  have h := riemann_roch_P1 k d
  have h2 := serre_duality_P1 k d


  rw [show (dimH1 k d : ℤ) = (dimH0 k (-2 - d) : ℤ) from congrArg _ h2] at h
  exact h


/-- The genus of a line `ℓ ⊆ ℙ²` agrees with `dim H^1(𝒪_{ℙ¹}) = 0`. -/
theorem genus_line_eq_dimH1_P1 :
    (genus 1 : ℤ) = (dimH1 k (0 : ℤ) : ℤ) := by
  rw [genus_line, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, dimH1_nonneg]

/-- Consistency of the Euler characteristic with the genus formula for a line. -/
theorem genus_line_euler_consistency :
    euler_char k 0 = 1 - (genus 1 : ℤ) := by
  rw [euler_char_eq, genus_line]; ring

end RiemannRoch
