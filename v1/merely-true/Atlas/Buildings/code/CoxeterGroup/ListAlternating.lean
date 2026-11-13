/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

/-- A list whose entries are $2$-periodic ($w[k] = w[k+2]$ whenever both make sense) is
determined by its first two entries: $w[i] = w[0]$ if $i$ even, $w[1]$ if $i$ odd. -/
lemma list_skip_index {α : Type*}
    (w : List α) (hw : w.length ≥ 2)
    (h_skip : ∀ k (hk : k + 2 < w.length), w[k]'(by omega) = w[k+2]'(by omega)) :
    ∀ (i : ℕ) (hi : i < w.length),
    w[i]'hi = if i % 2 = 0 then w[0]'(by omega) else w[1]'(by omega) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    match i, ih with
    | 0, _ => simp
    | 1, _ => simp
    | i + 2, ih =>
      have hi2 : i < w.length := by omega
      have hskip := h_skip i (by omega)
      rw [← hskip, ih i (by omega) hi2]
      simp only [show (i + 2) % 2 = i % 2 from by omega]
