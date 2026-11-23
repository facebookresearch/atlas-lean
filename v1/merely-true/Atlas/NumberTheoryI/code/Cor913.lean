/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div

open Polynomial


theorem Polynomial.eval_and_derivative_eval_eq_zero_iff
    {R : Type*} [CommRing R] (f : R[X]) (a : R) :
    f.eval a = 0 ∧ f.derivative.eval a = 0 ↔ ∃ g : R[X], f = (X - C a) ^ 2 * g := by
  constructor
  ·
    rintro ⟨hf, hf'⟩

    have h0 : (taylor a f).coeff 0 = 0 := by rw [taylor_coeff_zero, hf]
    have h1 : (taylor a f).coeff 1 = 0 := by rw [taylor_coeff_one, hf']

    have hdvd : X ^ 2 ∣ taylor a f := by
      rw [X_pow_dvd_iff]
      intro d hd
      rcases d with _ | _ | _ <;> simp_all
    obtain ⟨g, hg⟩ := hdvd

    refine ⟨taylor (-a) g, ?_⟩
    have key : f = taylor (-a) (taylor a f) := by
      rw [taylor_taylor, neg_add_cancel, taylor_zero]
    rw [key, hg, taylor_mul, taylor_pow, taylor_X, map_neg, sub_eq_add_neg]
  ·
    rintro ⟨g, hg⟩
    refine ⟨?_, ?_⟩
    · rw [hg, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
        zero_pow (by norm_num : 2 ≠ 0), zero_mul]
    · rw [hg, derivative_mul, derivative_pow, eval_add, eval_mul, eval_mul]
      simp [eval_sub, eval_X, eval_C, sub_self]
