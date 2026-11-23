/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Complex

theorem exp_add_prop1 (z w : ℂ) : exp (z + w) = exp z * exp w :=
  exp_add z w

end Complex

open Real in
theorem rpow_eq_exp_mul_log (b : ℝ) (hb : 0 < b) (x : ℝ) :
    b ^ x = Real.exp (x * Real.log b) := by
  rw [rpow_def_of_pos hb, mul_comm]

open Real in
theorem rpow_add_mul (b : ℝ) (hb : 0 < b) (x y : ℝ) :
    b ^ (x + y) = b ^ x * b ^ y :=
  rpow_add hb x y

open Complex Real in
noncomputable def primitiveUnitRoot (n : ℕ) : ℂ := Complex.exp (2 * ↑π * I / ↑n)

theorem primitiveUnitRoot_isPrimitiveRoot (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot (primitiveUnitRoot n) n :=
  Complex.isPrimitiveRoot_exp n hn

theorem roots_of_unity_eq_powers_of_primitiveUnitRoot (n : ℕ) (hn : 0 < n) (z : ℂ) :
    z ^ n = 1 ↔ ∃ k : Fin n, z = (primitiveUnitRoot n) ^ (k : ℕ) := by
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hprim := primitiveUnitRoot_isPrimitiveRoot n hne
  constructor
  · intro hz
    haveI : NeZero n := ⟨hne⟩
    obtain ⟨i, hi, hiz⟩ := hprim.eq_pow_of_pow_eq_one hz
    exact ⟨⟨i, hi⟩, hiz.symm⟩
  · rintro ⟨k, rfl⟩
    show (primitiveUnitRoot n ^ (k : ℕ)) ^ n = 1
    unfold primitiveUnitRoot
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨(k : ℤ), ?_⟩
    push_cast
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hne
    field_simp

open Complex Real in
theorem Complex.log_mul_eq_add_log_add_int (z₁ z₂ : ℂ) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) :
    ∃ n : ℤ, n ∈ ({-1, 0, 1} : Set ℤ) ∧
      Complex.log (z₁ * z₂) = Complex.log z₁ + Complex.log z₂ + ↑n * (2 * ↑π * I) := by


  have h1 : exp (log (z₁ * z₂)) = exp (log z₁ + log z₂) := by
    rw [exp_log (mul_ne_zero hz₁ hz₂), Complex.exp_add, exp_log hz₁, exp_log hz₂]
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp h1
  refine ⟨n, ?_, hn⟩

  have him_n : arg (z₁ * z₂) = arg z₁ + arg z₂ + n * (2 * π) := by
    have := congr_arg Complex.im hn
    simp [log_im] at this
    linarith


  have hpi : (0 : ℝ) < π := pi_pos
  have hn_bound : -3 * π < n * (2 * π) ∧ n * (2 * π) < 3 * π := by
    constructor <;> nlinarith [neg_pi_lt_arg (z₁ * z₂), arg_le_pi (z₁ * z₂),
      neg_pi_lt_arg z₁, neg_pi_lt_arg z₂, arg_le_pi z₁, arg_le_pi z₂]
  have hn_le : n ≤ 1 := by
    by_contra h
    push Not at h
    have : (2 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith
  have hn_ge : -1 ≤ n := by
    by_contra h
    push Not at h
    have : n ≤ -2 := by omega
    have : (n : ℝ) ≤ -2 := by exact_mod_cast this
    nlinarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega
