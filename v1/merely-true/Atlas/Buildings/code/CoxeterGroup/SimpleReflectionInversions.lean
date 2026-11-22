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


/-- Appending $s$ at the end of a word negates the geometric action on $e_s$:
$(w \cdot s) \cdot e_s = -(w \cdot e_s)$. -/
theorem wordSigma_append_s_neg (M : CoxeterMatrix B) (word : List B) (s : B) :
    wordSigma M (word ++ [s]) (e s) = fun t => -(wordSigma M word (e s) t) := by
  rw [wordSigma_append, wordSigma_singleton, sigma_e_self]
  have h : (fun t => -(e s t)) = (-1 : ℝ) • e s := by
    ext t; simp [Pi.smul_apply, smul_eq_mul]
  rw [h, wordSigma_smul]
  ext t
  simp [Pi.smul_apply, smul_eq_mul]

/-- The inversion set of the singleton word $[s]$ is exactly $\{s\}$. -/
theorem bilinInversions_singleton (M : CoxeterMatrix B) (s : B) :
    bilinInversions M [s] = {s} := by
  ext t
  simp only [Finset.mem_singleton]
  constructor
  ·
    intro ht
    by_contra hne
    exact t_not_in_bilinInversions_singleton M s t (Ne.symm hne) ht
  ·
    intro ht
    rw [ht]
    exact s_in_bilinInversions_singleton M s

end CoxeterGroup
