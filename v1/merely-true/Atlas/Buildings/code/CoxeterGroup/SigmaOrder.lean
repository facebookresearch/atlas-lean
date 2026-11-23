/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.Basic

open Finset BigOperators

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The simple reflection $\sigma_s$ packaged as an $\mathbb{R}$-linear endomorphism of $\mathbb{R}^B$. -/
noncomputable def sigmaLin (M : CoxeterMatrix B) (s : B) : Module.End ℝ (B → ℝ) where
  toFun := sigma M s
  map_add' := by
    intro v w; ext t
    simp only [sigma, bilinForm, Pi.add_apply]
    simp_rw [add_mul, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro r v; ext t
    simp only [sigma, bilinForm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have : (∑ x : B, ∑ x_1 : B, r * v x * formVal M x x_1 * e s x_1) =
        r * (∑ x : B, ∑ x_1 : B, v x * formVal M x x_1 * e s x_1) := by
      rw [Finset.mul_sum]; congr 1; funext x
      rw [Finset.mul_sum]; congr 1; funext x_1; ring
    rw [this]; ring

/-- General reflection formula: $\langle \sigma_t v, e_s\rangle = \langle v, e_s\rangle
- 2\langle v, e_t\rangle\langle e_t, e_s\rangle$. -/
theorem bilinForm_sigma_general (M : CoxeterMatrix B) (s t : B) (v : B → ℝ) :
    bilinForm M (sigma M t v) (e s) =
      bilinForm M v (e s) - 2 * bilinForm M v (e t) * formVal M t s := by
  simp only [bilinForm, sigma]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  congr 1
  simp_rw [e, Pi.single_apply]
  simp_rw [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp [Finset.sum_ite_eq']

/-- The simple reflection negates the pairing against its own simple root:
$\langle \sigma_s v, e_s\rangle = -\langle v, e_s\rangle$. -/
theorem bilinForm_sigma_e (M : CoxeterMatrix B) (s : B) (v : B → ℝ) :
    bilinForm M (sigma M s v) (e s) = -bilinForm M v (e s) := by
  rw [bilinForm_sigma_general, formVal_diag]
  ring

/-- Simple reflections are involutions: $\sigma_s^2 = \mathrm{id}$. -/
theorem sigma_sq (M : CoxeterMatrix B) (s : B) :
    sigmaLin M s * sigmaLin M s = 1 := by
  apply LinearMap.ext; intro v
  change sigma M s (sigma M s v) = v
  ext t
  simp only [sigma, bilinForm_sigma_e]
  ring

/-- $\sigma_s$ sends its simple root $e_s$ to $-e_s$. -/
theorem sigmaLin_e_self (M : CoxeterMatrix B) (s : B) :
    sigmaLin M s (e s) = -e s := by
  ext t
  show sigma M s (e s) t = (-e s) t
  simp only [sigma, bilinForm_e_e, formVal_diag, Pi.neg_apply]
  ring

/-- Coordinate formula for the action of $\sigma_s$ on a distinct simple root $e_t$. -/
theorem sigmaLin_e (M : CoxeterMatrix B) (s t : B) (_hst : s ≠ t) :
    sigmaLin M s (e t) = fun u => e t u - 2 * formVal M s t * e s u := by
  ext u
  show sigma M s (e t) u = e t u - 2 * formVal M s t * e s u
  simp only [sigma, bilinForm_e_e, formVal_symm M t s]

end CoxeterGroup
