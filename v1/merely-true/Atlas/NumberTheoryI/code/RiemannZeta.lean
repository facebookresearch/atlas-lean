/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex Filter Topology Nat

namespace RiemannZetaFunction

theorem riemannZeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (↑n : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_cpow hs

theorem riemannZeta_eulerProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - (↑(↑p) : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
  _root_.riemannZeta_eulerProduct_hasProd hs

theorem riemannZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  _root_.riemannZeta_ne_zero_of_one_lt_re hs

theorem riemannZeta_eulerProduct_and_nonvanishing {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - (↑(↑p) : ℂ) ^ (-s))⁻¹) (riemannZeta s) ∧
      riemannZeta s ≠ 0 :=
  ⟨riemannZeta_eulerProduct_hasProd hs, riemannZeta_ne_zero_of_one_lt_re hs⟩

theorem riemannZeta_differentiableAt {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

theorem riemannZeta_residue_eq_one :
    Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  riemannZeta_residue_one

theorem riemannZeta_meromorphic_with_residue :
    (∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ riemannZeta s) ∧
    Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  ⟨fun _ hs ↦ riemannZeta_differentiableAt hs, riemannZeta_residue_eq_one⟩

theorem mertens_norm_zeta_product_ge_one (x y : ℝ) (hx : 1 < x) :
    ‖riemannZeta (↑x) ^ 3 * riemannZeta (↑x + ↑y * Complex.I) ^ 4 *
      riemannZeta (↑x + 2 * ↑y * Complex.I)‖ ≥ 1 := by

  have hx'_pos : (0 : ℝ) < x - 1 := by linarith

  have hmathlib := DirichletCharacter.norm_LFunction_product_ge_one
    (1 : DirichletCharacter ℂ 1) hx'_pos y

  simp only [DirichletCharacter.LFunction_modOne_eq] at hmathlib

  have harg : (1 : ℂ) + (↑(x - 1) : ℂ) = ↑x := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one]; ring
  rw [harg] at hmathlib

  convert hmathlib using 3 <;> ring_nf

theorem riemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  _root_.riemannZeta_ne_zero_of_one_le_re hs

end RiemannZetaFunction
