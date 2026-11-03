/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace ProjectionTheory

/-- **Grid projection bound** (Example 3, Szemerédi–Trotter application). The image of the
$N \times N$ integer grid under the linear projection $(x, y) \mapsto by - ax$ with
$|a|, |b| \le M$ has cardinality at most $(2M + 1)N$; in particular,
$|\pi_s(X)| \lesssim MN$ for slopes $s = a/b$ with $|a|, |b| \le M$. -/
theorem grid_projection_bound (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (a b : ℤ) (hb : b ≠ 0) (ha : |a| ≤ M) (hbb : |b| ≤ M) :
    (Finset.image (fun p : Fin N × Fin N => b * (p.2 : ℤ) - a * (p.1 : ℤ))
      Finset.univ).card ≤ (2 * M + 1) * N := by
  set S := Finset.image (fun p : Fin N × Fin N => b * (p.2 : ℤ) - a * (p.1 : ℤ)) Finset.univ
  by_cases hS : S.Nonempty
  ·
    have h_sub : S ⊆ Finset.Icc (S.min' hS) (S.max' hS) := fun x hx =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le S x hx, Finset.le_max' S x hx⟩

    have h_width : S.max' hS - S.min' hS ≤ 2 * (M : ℤ) * ((N : ℤ) - 1) := by
      obtain ⟨pmax, _, hpmax⟩ := Finset.mem_image.mp (Finset.max'_mem S hS)
      obtain ⟨pmin, _, hpmin⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
      rw [← hpmax, ← hpmin]


      have hd₂ : |(pmax.2 : ℤ) - (pmin.2 : ℤ)| ≤ (N : ℤ) - 1 := by
        rw [abs_le]
        constructor <;> (have := pmax.2.isLt; have := pmin.2.isLt; omega)
      have hd₁ : |(pmax.1 : ℤ) - (pmin.1 : ℤ)| ≤ (N : ℤ) - 1 := by
        rw [abs_le]
        constructor <;> (have := pmax.1.isLt; have := pmin.1.isLt; omega)
      have habs : |b * ((pmax.2 : ℤ) - pmin.2) + (-(a * ((pmax.1 : ℤ) - pmin.1)))| ≤
          2 * (M : ℤ) * ((N : ℤ) - 1) :=
        calc |b * ((pmax.2 : ℤ) - pmin.2) + (-(a * ((pmax.1 : ℤ) - pmin.1)))|
            ≤ |b * ((pmax.2 : ℤ) - pmin.2)| + |-(a * ((pmax.1 : ℤ) - pmin.1))| :=
              abs_add_le _ _
          _ = |b| * |(pmax.2 : ℤ) - pmin.2| + |a| * |(pmax.1 : ℤ) - pmin.1| := by
              rw [abs_neg, abs_mul, abs_mul]
          _ ≤ (M : ℤ) * ((N : ℤ) - 1) + (M : ℤ) * ((N : ℤ) - 1) := by gcongr
          _ = 2 * (M : ℤ) * ((N : ℤ) - 1) := by ring
      linarith [le_abs_self (b * ((pmax.2 : ℤ) - pmin.2) + (-(a * ((pmax.1 : ℤ) - pmin.1))))]

    calc S.card
        ≤ (Finset.Icc (S.min' hS) (S.max' hS)).card := Finset.card_le_card h_sub
      _ = (S.max' hS + 1 - S.min' hS).toNat := by simp [Int.card_Icc]
      _ ≤ (2 * (M : ℤ) * ((N : ℤ) - 1) + 1).toNat := by
          apply Int.toNat_le_toNat; linarith
      _ ≤ (2 * M + 1) * N := by
          have h : 2 * (M : ℤ) * ((N : ℤ) - 1) + 1 ≤ ↑((2 * M + 1) * N) := by
            push_cast; nlinarith [show (1 : ℤ) ≤ (N : ℤ) from by exact_mod_cast hN]
          exact_mod_cast Int.toNat_le.mpr h
  ·
    rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty]
    exact Nat.zero_le _

end ProjectionTheory
