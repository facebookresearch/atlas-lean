/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation

open Finset BigOperators

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The bilinear inversion set of a word $w$: the set of $s \in S$ for which the
$s$-component of $\sigma_w(\alpha_s)$ is strictly negative. -/
noncomputable def bilinInversions (M : CoxeterMatrix B) (word : List B) : Finset B :=
  Finset.univ.filter (fun s => wordSigma M word (e s) s < 0)


/-- The empty word has empty inversion set. -/
theorem bilinInversions_nil (M : CoxeterMatrix B) :
    bilinInversions M ([] : List B) = ∅ := by
  simp only [bilinInversions, Finset.filter_eq_empty_iff]
  intro s _
  simp only [wordSigma_nil, not_lt]

  have : e s s = 1 := by simp [e, Pi.single_apply]
  linarith


/-- The singleton word $[s]$ has $s$ as an inversion. -/
theorem s_in_bilinInversions_singleton (M : CoxeterMatrix B) (s : B) :
    s ∈ bilinInversions M [s] := by
  simp only [bilinInversions, Finset.mem_filter, Finset.mem_univ, true_and,
    wordSigma_singleton]
  rw [sigma_e_self]

  simp only [e, Pi.single_apply, if_pos rfl, neg_lt_zero]
  norm_num


/-- For $s \neq t$, the $t$-component of $\sigma_s(\alpha_t)$ equals $1$. -/
theorem sigma_e_other_t_component' (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t) :
    sigma M s (e t) t = 1 := by
  simp only [sigma, bilinForm_e_e, e, Pi.single_apply]
  simp only [if_true, ite_not, Ne.symm hst, ite_false]
  ring


/-- For $s \neq t$, the singleton word $[s]$ does not have $t$ as an inversion. -/
theorem t_not_in_bilinInversions_singleton (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t) :
    t ∉ bilinInversions M [s] := by
  simp only [bilinInversions, Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
    wordSigma_singleton]
  rw [sigma_e_other_t_component' M s t hst]
  norm_num

/-- Membership in the bilinear inversion set: $s \in \mathrm{Inv}(w) \iff (\sigma_w \alpha_s)_s < 0$. -/
theorem mem_bilinInversions_iff (M : CoxeterMatrix B) (word : List B) (s : B) :
    s ∈ bilinInversions M word ↔ wordSigma M word (e s) s < 0 := by
  simp [bilinInversions]

end CoxeterGroup
