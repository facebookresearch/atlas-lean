/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.BigOperators

open Finset BigOperators

namespace CoxeterGroup

variable {B : Type*}

/-- Entry $B_{s,t}$ of the bilinear form on the geometric representation. -/
noncomputable def formVal (M : CoxeterMatrix B) (s t : B) : ℝ :=
  if M s t = 0 then -1
  else -Real.cos (Real.pi / (M s t : ℝ))

/-- Symmetry: $B_{s,t} = B_{t,s}$. -/
theorem formVal_symm (M : CoxeterMatrix B) (s t : B) :
    formVal M s t = formVal M t s := by
  simp only [formVal, M.symmetric s t]

/-- Diagonal value: $B_{s,s} = 1$. -/
theorem formVal_diag (M : CoxeterMatrix B) (s : B) :
    formVal M s s = 1 := by
  simp only [formVal, M.diagonal s]
  norm_num

variable [DecidableEq B] [Fintype B]

/-- The bilinear form on $\mathbb{R}^B$ associated to the Coxeter matrix $M$,
defined by $B(v, w) = \sum_{s,t} v_s\, B_{s,t}\, w_t$ where
$B_{s,t} = \mathtt{formVal}\,M\,s\,t$. This is the standard form making the
geometric representation orthogonal. -/
noncomputable def bilinForm (M : CoxeterMatrix B) (v w : B → ℝ) : ℝ :=
  ∑ s, ∑ t, v s * formVal M s t * w t

/-- The standard basis vector $e_s \in \mathbb{R}^B$ supported at $s$ with value
$1$. -/
noncomputable def e (s : B) : B → ℝ := Pi.single s 1

/-- Evaluating the bilinear form on basis vectors recovers the matrix entry:
$B(e_s, e_t) = B_{s,t}$. -/
theorem bilinForm_e_e (M : CoxeterMatrix B) (s t : B) :
    bilinForm M (e s) (e t) = formVal M s t := by
  simp only [bilinForm, e]
  simp_rw [Pi.single_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']

/-- The reflection $\sigma_s$ on $\mathbb{R}^B$ associated to a simple generator
$s$: $\sigma_s(v) = v - 2\, B(v, e_s)\, e_s$. This is the simple reflection in
the geometric representation. -/
noncomputable def sigma (M : CoxeterMatrix B) (s : B) (v : B → ℝ) : B → ℝ :=
  fun t => v t - 2 * bilinForm M v (e s) * e s t

/-- The reflection $\sigma_s$ negates $e_s$: $\sigma_s(e_s) = -e_s$. -/
theorem sigma_e_self (M : CoxeterMatrix B) (s : B) :
    sigma M s (e s) = fun t => -(e s t) := by
  ext t
  simp only [sigma, bilinForm_e_e, formVal_diag]
  ring

end CoxeterGroup
