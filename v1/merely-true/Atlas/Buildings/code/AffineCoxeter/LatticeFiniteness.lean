/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Int.Order.Lemmas

open Finset in
/-- **Lattice finiteness lemma**: a set of integral nonnegative vectors $S \subseteq \mathbb Z_{\ge 0}^B$
with $f(\alpha, \alpha) \le C$ is finite, provided $f$ is coercive ($c\|v\|^2 \le f(v,v)$). This is
the abstract finiteness principle underlying the finiteness of root systems on hyperplanes. -/
theorem finite_nonneg_bounded_of_pd
    {B : Type*} [Fintype B]
    (f : (B → ℝ) → (B → ℝ) → ℝ)
    (C : ℝ)
    (c : ℝ) (hc : 0 < c)
    (hcoerce : ∀ v : B → ℝ, c * ∑ b : B, (v b) ^ 2 ≤ f v v)
    (S : Set (B → ℝ))
    (hS_nn : ∀ α ∈ S, ∀ b : B, 0 ≤ α b)
    (hS_bdd : ∀ α ∈ S, f α α ≤ C)
    (hS_discrete : ∀ b : B, ∀ α ∈ S, ∃ n : ℤ, α b = ↑n)
    : S.Finite := by

  have hL2 : ∀ α ∈ S, ∑ b : B, (α b) ^ 2 ≤ C / c := by
    intro α hα
    have h1 := hcoerce α
    have h2 := hS_bdd α hα
    have hle : c * ∑ b : B, (α b) ^ 2 ≤ C := le_trans h1 h2
    have : c * (∑ b : B, (α b) ^ 2) / c ≤ C / c :=
      div_le_div_of_nonneg_right hle hc.le
    rwa [mul_div_cancel_left₀ _ (ne_of_gt hc)] at this

  have hcoord_sq : ∀ α ∈ S, ∀ b : B, (α b) ^ 2 ≤ C / c := by
    intro α hα b
    calc (α b) ^ 2
        ≤ ∑ b' : B, (α b') ^ 2 :=
          single_le_sum (fun i _ => sq_nonneg (α i)) (mem_univ b)
      _ ≤ C / c := hL2 α hα

  have hcoord : ∀ α ∈ S, ∀ b : B, α b ≤ Real.sqrt (C / c) := by
    intro α hα b
    rw [← Real.sqrt_sq (hS_nn α hα b)]
    exact Real.sqrt_le_sqrt (hcoord_sq α hα b)

  set bound := Real.sqrt (C / c)
  set T : B → Set ℝ := fun _ =>
    {x : ℝ | (∃ n : ℤ, x = ↑n) ∧ 0 ≤ x ∧ x ≤ bound}
  have hT_finite : ∀ b : B, (T b).Finite := by
    intro b
    apply Set.Finite.subset
      ((Set.finite_Icc (0 : ℤ) ⌊bound⌋).image (Int.cast : ℤ → ℝ))
    intro x ⟨⟨n, hn⟩, hx0, hxM⟩
    exact ⟨n, ⟨by exact_mod_cast hn ▸ hx0, Int.le_floor.mpr (hn ▸ hxM)⟩, hn.symm⟩
  have hS_sub : S ⊆ Set.univ.pi T := by
    intro α hα b _
    exact ⟨hS_discrete b α hα, hS_nn α hα b, hcoord α hα b⟩
  exact (Set.Finite.pi hT_finite).subset hS_sub
