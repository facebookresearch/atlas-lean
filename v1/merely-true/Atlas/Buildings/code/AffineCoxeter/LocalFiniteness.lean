/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.TitsConeCorollary

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The pairing is linear in the second argument, so if $\langle \alpha, y\rangle > 0$ and
$\langle \alpha, z\rangle > 0$ then $\langle \alpha, (1-t)y + tz\rangle > 0$ for any $t \in [0,1]$. -/
lemma pairing_convex_combination_pos
    (α y z : B → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hy : pairing α y > 0) (hz : pairing α z > 0) :
    pairing α (fun s => (1 - t) * y s + t * z s) > 0 := by
  unfold pairing
  have hconv : ∑ s : B, α s * ((1 - t) * y s + t * z s) =
      (1 - t) * (∑ s : B, α s * y s) + t * (∑ s : B, α s * z s) := by
    have h : ∀ s : B, α s * ((1 - t) * y s + t * z s) =
        (1 - t) * (α s * y s) + t * (α s * z s) := fun s => by ring
    simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hconv]
  have h1 : (1 - t) * (∑ s : B, α s * y s) ≥ 0 :=
    mul_nonneg (by linarith) (le_of_lt hy)
  by_cases ht_eq : t = 0
  · rw [ht_eq]; simp; exact hy
  · have : t * (∑ s : B, α s * z s) > 0 :=
      mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht_eq)) hz
    linarith

/-- Contrapositive: if a reflecting hyperplane $\{x : \langle\alpha, x\rangle = 0\}$ meets the segment
$[y, z]$, then at least one endpoint satisfies $\langle\alpha, \cdot\rangle \le 0$. -/
lemma hyperplane_meets_segment_implies_nonpos
    (α y z : B → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : pairing α (fun s => (1 - t) * y s + t * z s) = 0) :
    pairing α y ≤ 0 ∨ pairing α z ≤ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨hy, hz⟩ := hc
  have := pairing_convex_combination_pos α y z t ht0 ht1 hy hz
  linarith

/-- **Local finiteness**: any segment $[y,z] \subset \mathcal U \setminus \{0\}$ meets only finitely
many reflecting hyperplanes. The proof bounds these roots by the union of nonposRoots at the two
endpoints, both of which are finite. -/
theorem segment_meets_finite_roots
    (M : CoxeterMatrix B) [Nonempty B] [inst : RootSystemData M]
    (v₀ : B → ℝ) (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
    (y z : B → ℝ)
    (hy : y ∈ titsConeSet M \ {0})
    (hz : z ∈ titsConeSet M \ {0}) :
    Set.Finite {α ∈ inst.Φpos |
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        pairing α (fun s => (1 - t) * y s + t * z s) = 0} := by
  apply Set.Finite.subset
    ((nuFiniteAt_of_mem_titsCone_sdiff_zero M v₀ hv₀_pos hv₀_rad y hy).union
     (nuFiniteAt_of_mem_titsCone_sdiff_zero M v₀ hv₀_pos hv₀_rad z hz))
  intro α ⟨hα_mem, t, ht0, ht1, hpair⟩
  have h := hyperplane_meets_segment_implies_nonpos α y z t ht0 ht1 hpair
  simp only [Set.mem_union, nonposRoots, Set.mem_sep_iff]
  rcases h with h | h
  · left; exact ⟨hα_mem, h⟩
  · right; exact ⟨hα_mem, h⟩

end TitsCone
