/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination

open Polynomial

section FormalDerivative

variable {R : Type*}

theorem formalDerivative_linear [CommRing R] (a b : R) (f g : R[X]) :
    derivative (C a * f + C b * g) = C a * derivative f + C b * derivative g := by
  simp [derivative_add]

end FormalDerivative

section TaylorExpansion

variable {R : Type*} [CommRing R]

theorem taylor_expansion (f : R[X]) (a : R) :
    ∃! g : R[X], f = C (f.eval a) + C ((derivative f).eval a) * (X - C a) +
      g * (X - C a) ^ 2 := by

  have h1 : (X - C a) ∣ (f - C (f.eval a)) := dvd_iff_isRoot.mpr (by simp [IsRoot])
  obtain ⟨q1, hq1⟩ := h1

  have hq1a : q1.eval a = (derivative f).eval a := by
    have hderiv : derivative (f - C (f.eval a)) = derivative ((X - C a) * q1) := by rw [hq1]
    rw [derivative_sub, derivative_C, sub_zero, derivative_mul] at hderiv
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero] at hderiv
    have := congr_arg (fun p => p.eval a) hderiv
    simp [eval_add, eval_mul, eval_sub, eval_X, eval_C] at this
    exact this.symm

  have h2 : (X - C a) ∣ (q1 - C ((derivative f).eval a)) := by
    rw [dvd_iff_isRoot]; simp [IsRoot, hq1a]
  obtain ⟨g, hg⟩ := h2

  refine ⟨g, by linear_combination hq1 + (X - C a) * hg, ?_⟩

  intro g' hg'
  have key : f = C (f.eval a) + C ((derivative f).eval a) * (X - C a) +
      g * (X - C a) ^ 2 := by linear_combination hq1 + (X - C a) * hg
  have heq : g' * (X - C a) ^ 2 = g * (X - C a) ^ 2 := add_left_cancel (hg'.symm.trans key)
  have hmonic : ((X - C a) ^ 2).Monic := (monic_X_sub_C a).pow 2
  have h3 : (g' - g) * (X - C a) ^ 2 = 0 := by rw [sub_mul, heq, sub_self]
  rwa [hmonic.mul_left_eq_zero_iff, sub_eq_zero] at h3

end TaylorExpansion

section SimpleRoot

variable {R : Type*} [CommRing R]

def IsSimpleRoot (f : R[X]) (a : R) : Prop :=
  f.eval a = 0 ∧ (derivative f).eval a ≠ 0

end SimpleRoot
