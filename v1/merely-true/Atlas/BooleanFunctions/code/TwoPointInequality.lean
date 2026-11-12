/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real Set

namespace BooleanFourier

noncomputable def twoPointLpNorm (p : ℝ) (g : Bool → ℝ) : ℝ :=
  ((|g true| ^ p + |g false| ^ p) / 2) ^ (1 / p)

noncomputable def twoPointNoiseOp (ρ : ℝ) (g : Bool → ℝ) : Bool → ℝ :=
  fun b => if b then ((1 + ρ) / 2) * g true + ((1 - ρ) / 2) * g false
           else ((1 - ρ) / 2) * g true + ((1 + ρ) / 2) * g false




section PathFunction

set_option maxHeartbeats 800000

noncomputable def twoPointPathFn (p : ℝ) (a b : ℝ) (t : ℝ) : ℝ :=
  let r := 1 + (p - 1) / t ^ 2
  let c := (1 + t) / 2 * a + (1 - t) / 2 * b
  let d := (1 - t) / 2 * a + (1 + t) / 2 * b
  ((c ^ r + d ^ r) / 2) ^ (1 / r)

noncomputable def twoPointExponent (p : ℝ) (t : ℝ) : ℝ :=
  1 + (p - 1) / t ^ 2

lemma twoPointPathFn_c_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    0 < (1 + t) / 2 * a + (1 - t) / 2 * b := by
  have h1 : (0 : ℝ) < (1 + t) / 2 := by linarith [ht.1]
  have h2 : (0 : ℝ) < (1 - t) / 2 := by linarith [ht.2]
  rcases ha.lt_or_eq with ha_pos | ha_zero
  · linarith [mul_pos h1 ha_pos, mul_nonneg h2.le hb]
  · linarith [mul_nonneg h1.le ha, mul_pos h2 (show (0 : ℝ) < b by linarith [ha_zero.symm])]

lemma twoPointPathFn_d_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    0 < (1 - t) / 2 * a + (1 + t) / 2 * b := by
  have h1 : (0 : ℝ) < (1 - t) / 2 := by linarith [ht.2]
  have h2 : (0 : ℝ) < (1 + t) / 2 := by linarith [ht.1]
  rcases ha.lt_or_eq with ha_pos | ha_zero
  · linarith [mul_pos h1 ha_pos, mul_nonneg h2.le hb]
  · linarith [mul_nonneg h1.le ha, mul_pos h2 (show (0 : ℝ) < b by linarith [ha_zero.symm])]

lemma twoPointPathFn_base_pos {p a b : ℝ} (_hp : 1 < p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    0 < (((1 + t) / 2 * a + (1 - t) / 2 * b) ^ (1 + (p - 1) / t ^ 2) +
         ((1 - t) / 2 * a + (1 + t) / 2 * b) ^ (1 + (p - 1) / t ^ 2)) / 2 :=
  div_pos (add_pos_of_pos_of_nonneg
    (rpow_pos_of_pos (twoPointPathFn_c_pos ha hb hab ht) _)
    (rpow_nonneg (twoPointPathFn_d_pos ha hb hab ht).le _)) two_pos

noncomputable def twoPointPathFn_derivValue (p a b t : ℝ) : ℝ :=
  let r := 1 + (p - 1) / t ^ 2
  let c := (1 + t) / 2 * a + (1 - t) / 2 * b
  let d := (1 - t) / 2 * a + (1 + t) / 2 * b
  let S := c ^ r + d ^ r
  let F := (S / 2) ^ (1 / r)
  let r' := -2 * (p - 1) / t ^ 3
  let c' := (a - b) / 2
  let d' := (b - a) / 2
  F * (1 / r * (r * c ^ (r - 1) * c' + r * d ^ (r - 1) * d') / S
      - r' / r ^ 2 * Real.log (S / 2))

end PathFunction

end BooleanFourier
