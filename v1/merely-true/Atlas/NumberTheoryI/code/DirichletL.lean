/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex Filter Topology Nat

open scoped LSeries.notation

noncomputable section

namespace DirichletLFunction

abbrev DirichletCharacterMod (N : ℕ) := DirichletCharacter ℂ N

theorem dirichletLFunction_eq_LSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = LSeries (χ ·) s :=
  DirichletCharacter.LFunction_eq_LSeries χ hs

@[deprecated (since := "2024-12-18")]
alias def_18_19_L_function_eq_dirichlet_series := dirichletLFunction_eq_LSeries

theorem dirichletLSeries_eulerProduct_hasProd {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - χ p * (p : ℂ) ^ (-s))⁻¹) (L ↗χ s) :=
  DirichletCharacter.LSeries_eulerProduct_hasProd χ hs

@[deprecated (since := "2024-12-18")]
alias def_18_19_euler_product_hasProd := dirichletLSeries_eulerProduct_hasProd

theorem dirichletLSeries_eulerProduct_tprod {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - χ p * (p : ℂ) ^ (-s))⁻¹ = L ↗χ s :=
  DirichletCharacter.LSeries_eulerProduct_tprod χ hs

@[deprecated (since := "2024-12-18")]
alias def_18_19_euler_product_tprod := dirichletLSeries_eulerProduct_tprod

theorem dirichletLSeries_eulerProduct {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - χ p * (p : ℂ) ^ (-s))⁻¹)
      atTop (𝓝 (L ↗χ s)) :=
  DirichletCharacter.LSeries_eulerProduct χ hs

@[deprecated (since := "2024-12-18")]
alias def_18_19_euler_product := dirichletLSeries_eulerProduct

theorem dirichletLFunction_differentiableAt {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (DirichletCharacter.LFunction χ) s :=
  DirichletCharacter.differentiableAt_LFunction χ s (Or.inl (by
    intro h; rw [h] at hs; simp at hs))

@[deprecated (since := "2024-12-18")]
alias def_18_19_L_function_holomorphic := dirichletLFunction_differentiableAt

theorem dirichletLSeries_ne_zero_of_one_lt_re {N : ℕ}
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    L ↗χ s ≠ 0 :=
  DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs

@[deprecated (since := "2024-12-18")]
alias def_18_19_L_function_ne_zero_of_one_lt_re := dirichletLSeries_ne_zero_of_one_lt_re

theorem dirichletLFunction_modOne_eq_riemannZeta {χ : DirichletCharacter ℂ 1} :
    DirichletCharacter.LFunction χ = riemannZeta :=
  DirichletCharacter.LFunction_modOne_eq

@[deprecated (since := "2024-12-18")]
alias L_trivial_eq_zeta := dirichletLFunction_modOne_eq_riemannZeta

theorem dirichletLFunction_differentiable_of_ne_one {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (DirichletCharacter.LFunction χ) :=
  DirichletCharacter.differentiable_LFunction hχ

@[deprecated (since := "2024-12-18")]
alias prop_18_20_differentiable_LFunction := dirichletLFunction_differentiable_of_ne_one

theorem dirichletLFunction_ne_zero_at_one {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero hχ

@[deprecated (since := "2024-12-18")]
alias thm_18_key_L_one_ne_zero := dirichletLFunction_ne_zero_at_one

theorem dirichletLFunction_ne_zero_of_one_le_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs hs

@[deprecated (since := "2024-12-18")]
alias thm_18_key_L_ne_zero_of_one_le_re := dirichletLFunction_ne_zero_of_one_le_re

theorem infinite_primes_in_residueClass_zmod {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite :=
  Nat.infinite_setOf_prime_and_eq_mod ha

@[deprecated (since := "2024-12-18")]
alias thm_18_1_dirichlet_zmod := infinite_primes_in_residueClass_zmod

theorem exists_prime_gt_and_zmodEq (n : ℕ) {q : ℕ} {a : ℤ}
    (hq : q ≠ 0) (h : IsCoprime a q) :
    ∃ p > n, p.Prime ∧ ↑p ≡ a [ZMOD (q : ℤ)] :=
  Nat.forall_exists_prime_gt_and_zmodEq n hq h

@[deprecated (since := "2024-12-18")]
alias thm_18_1_dirichlet_int := exists_prime_gt_and_zmodEq

theorem exists_prime_gt_and_modEq (n : ℕ) {q a : ℕ}
    (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ p > n, p.Prime ∧ p ≡ a [MOD q] :=
  Nat.forall_exists_prime_gt_and_modEq n hq h

@[deprecated (since := "2024-12-18")]
alias thm_18_1_dirichlet := exists_prime_gt_and_modEq

theorem infinite_primes_in_arithmeticProgression {q a : ℕ}
    (hq : q ≠ 0) (h : a.Coprime q) :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD q]} :=
  Nat.infinite_setOf_prime_and_modEq hq h

@[deprecated (since := "2024-12-18")]
alias thm_18_1_dirichlet_infinite := infinite_primes_in_arithmeticProgression

theorem frequently_prime_and_modEq {q a : ℕ}
    (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ᶠ p in atTop, p.Prime ∧ p ≡ a [MOD q] :=
  Nat.frequently_atTop_prime_and_modEq hq h

@[deprecated (since := "2024-12-18")]
alias thm_18_1_dirichlet_frequently := frequently_prime_and_modEq

theorem dirichletLSeries_changeLevel {M N : ℕ} [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗(DirichletCharacter.changeLevel hMN χ)) s =
      LSeries ↗χ s * ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)) :=
  DirichletCharacter.LSeries_changeLevel hMN χ hs

@[deprecated (since := "2024-12-18")]
alias L_series_change_level := dirichletLSeries_changeLevel

end DirichletLFunction

end
