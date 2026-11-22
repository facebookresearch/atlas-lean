/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.InversionSet

open Finset BigOperators

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


omit [Fintype B] in

/-- Rewrites the pointwise negation of $\alpha_s$ as scalar multiplication by $-1$. -/
theorem neg_e_eq_neg_one_smul_e (s : B) :
    (fun t => -(e s t)) = (-1 : ℝ) • e s := by
  ext t; simp [Pi.smul_apply, smul_eq_mul]


/-- The $s$-component of $\sigma_{w \cdot s}(\alpha_s)$ flips sign under appending $s$:
$(w s)\cdot \alpha_s$ has $s$-component $-(w \cdot \alpha_s)_s$. -/
theorem wordSigma_append_s_component_neg (M : CoxeterMatrix B) (word : List B) (s : B) :
    wordSigma M (word ++ [s]) (e s) s = -(wordSigma M word (e s) s) := by
  rw [wordSigma_append, wordSigma_singleton, sigma_e_self, neg_e_eq_neg_one_smul_e,
      wordSigma_smul]
  simp [Pi.smul_apply, smul_eq_mul]

/-- Right-multiplication by $s$ toggles whether $s$ lies in the bilinear-inversion set:
$s \in \mathrm{Inv}(w s) \iff s \notin \mathrm{Inv}(w)$, provided the $s$-component is
nonzero. -/
theorem bilinInversions_append_toggle (M : CoxeterMatrix B) (word : List B) (s : B)
    (hne : wordSigma M word (e s) s ≠ 0) :
    s ∈ bilinInversions M (word ++ [s]) ↔ s ∉ bilinInversions M word := by
  rw [mem_bilinInversions_iff, mem_bilinInversions_iff]
  rw [wordSigma_append_s_component_neg]
  constructor
  · intro h_neg_lt h_lt
    linarith
  · intro h_not_lt
    push_neg at h_not_lt


    have hpos : wordSigma M word (e s) s > 0 := lt_of_le_of_ne h_not_lt (Ne.symm hne)
    linarith

end CoxeterGroup
