/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset BigOperators Real

/-- `a` is the (nonnegative) decreasing rearrangement of `|θ|`: it has the same
multiset of values as `|θ_i|`, is nonnegative, and is antitone. -/
structure IsDecreasingRearrangement {d : ℕ} (θ : Fin d → ℝ) (a : Fin d → ℝ) : Prop where
  nonneg : ∀ j, 0 ≤ a j
  antitone : Antitone a
  multiset_eq : Multiset.map a Finset.univ.val = Multiset.map (fun i => |θ i|) Finset.univ.val

/-- Weak `ℓ_q` norm of a rearranged vector `a`: `max_j (j+1)^{1/q} · a_j`. -/
noncomputable def weakLqNorm {d : ℕ} [NeZero d] (q : ℝ) (a : Fin d → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun j : Fin d => ((j.val + 1 : ℝ) ^ (1 / q)) * a j)

/-- Strong (standard) `ℓ_q` norm of `θ`: `(∑_i |θ_i|^q)^{1/q}`. -/
noncomputable def strongLqNorm {d : ℕ} (q : ℝ) (θ : Fin d → ℝ) : ℝ :=
  (∑ i : Fin d, |θ i| ^ q) ^ (1 / q)

/-- Membership in the weak `ℓ_q` ball of radius `R`: `a_j ≤ R · (j+1)^{-1/q}` for all `j`. -/
def InWeakLqBall {d : ℕ} (a : Fin d → ℝ) (q R : ℝ) : Prop :=
  ∀ j : Fin d, a j ≤ R * ((j.val + 1 : ℝ) ^ (-(1 / q)))

/-- If `a` and `b` give the same multiset of values when applied over `Finset.univ`,
then `∑ i, f(a i) = ∑ i, f(b i)` for any `f`. -/
lemma sum_comp_eq_of_multiset_map_eq {d : ℕ} (a b : Fin d → ℝ)
    (h : Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val)
    (f : ℝ → ℝ) :
    ∑ i, f (a i) = ∑ i, f (b i) := by
  have : Multiset.map f (Multiset.map a univ.val) =
         Multiset.map f (Multiset.map b univ.val) := by rw [h]
  rw [Multiset.map_map, Multiset.map_map] at this
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  exact congr_arg Multiset.sum this
