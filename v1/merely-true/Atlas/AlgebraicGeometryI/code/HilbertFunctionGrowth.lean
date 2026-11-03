/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Nat.Choose.Bounds

set_option maxHeartbeats 400000

noncomputable section

open Nat MvPolynomial

/-- Helper: `n^d ≤ (n+1)·(n+2)···(n+d)` (the ascending factorial). -/
lemma pow_le_ascFactorial_succ (n d : ℕ) : n ^ d ≤ (n + 1).ascFactorial d := by
  induction d with
  | zero => simp [Nat.ascFactorial]
  | succ d ih =>
    rw [pow_succ]
    calc n ^ d * n
        ≤ (n + 1).ascFactorial d * n := Nat.mul_le_mul_right n ih
      _ ≤ (n + 1).ascFactorial d * (n + 1 + d) := Nat.mul_le_mul_left _ (by omega)
      _ = (n + 1 + d) * (n + 1).ascFactorial d := by ring

/-- Helper polynomial-growth lower bound: `n^d ≤ d! · C(n+d, d)`. -/
theorem pow_le_factorial_mul_choose_add (n d : ℕ) :
    n ^ d ≤ d.factorial * (n + d).choose d := by
  calc n ^ d ≤ (n + 1).ascFactorial d := pow_le_ascFactorial_succ n d
    _ = d.factorial * (n + d).choose d := Nat.ascFactorial_eq_factorial_mul_choose n d

/-- Helper polynomial-growth upper bound: for `d ≤ n`, `C(n+d, d) ≤ 2^d · n^d`. -/
theorem choose_add_le_two_pow_mul_pow (n d : ℕ) (hnd : d ≤ n) :
    (n + d).choose d ≤ 2 ^ d * n ^ d := by
  calc (n + d).choose d ≤ (n + d) ^ d := Nat.choose_le_pow _ _
    _ ≤ (2 * n) ^ d := by apply Nat.pow_le_pow_left; omega
    _ = 2 ^ d * n ^ d := by ring

/-- The Hilbert function `n ↦ C(n+d, d)` of the polynomial ring in `d` variables;
the prototypical reference for `Θ(n^d)` growth. -/
def polyDimFun (d : ℕ) (n : ℕ) : ℕ := (n + d).choose d

/-- Filtration on `A` induced by an algebra surjection `f`: the `n`-th piece is the
image of polynomials of total degree `≤ n` under `f`. -/
def generatorFiltration {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
    {m : ℕ} (f : MvPolynomial (Fin m) k →ₐ[k] A) (n : ℕ) : Submodule k A :=
  Submodule.map f.toLinearMap (MvPolynomial.restrictTotalDegree (Fin m) k n)

/-- The Hilbert function `D_V(n)` for the filtration `generatorFiltration f`: the
`k`-dimension of its `n`-th piece. -/
def dimFun {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
    {m : ℕ} (f : MvPolynomial (Fin m) k →ₐ[k] A) (n : ℕ) : ℕ :=
  Module.finrank k (generatorFiltration f n)



