/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

structure DiscreteValuation (k : Type*) [Field k] where
  val : Valuation k (WithZero (Multiplicative ℤ))
  surj : Function.Surjective val

namespace DiscreteValuation

instance {k : Type*} [Field k] :
    FunLike (DiscreteValuation k) k (WithZero (Multiplicative ℤ)) where
  coe v := v.val
  coe_injective' := by
    intro v w h
    cases v; cases w
    simp only [mk.injEq]
    exact Valuation.ext (congrFun h)

instance {k : Type*} [Field k] :
    CoeOut (DiscreteValuation k) (Valuation k (WithZero (Multiplicative ℤ))) where
  coe v := v.val

end DiscreteValuation

def discreteValuationAbsoluteValueFun {k : Type*} [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    {c : NNReal} (hc : c ≠ 0) (x : k) : NNReal :=
  (WithZeroMulInt.toNNReal hc) (v x)

lemma isNonarchimedean_discreteValuationAbsoluteValueFun {k : Type*} [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    {c : NNReal} (hc : 1 < c) :
    IsNonarchimedean (discreteValuationAbsoluteValueFun v (ne_zero_of_lt hc)) := by
  intro x y
  simp only [discreteValuationAbsoluteValueFun]
  have h_mono := (WithZeroMulInt.toNNReal_strictMono hc).monotone
  rw [← h_mono.map_max]
  exact h_mono (v.map_add x y)

def discreteValuationAbsoluteValue {k : Type*} [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    {c : NNReal} (hc : 1 < c) : AbsoluteValue k ℝ where
  toFun x := discreteValuationAbsoluteValueFun v (ne_zero_of_lt hc) x
  map_mul' _ _ := by simp [discreteValuationAbsoluteValueFun]
  nonneg' _ := NNReal.coe_nonneg _
  eq_zero' _ := by simp [discreteValuationAbsoluteValueFun]
  add_le' _ _ :=
    (isNonarchimedean_discreteValuationAbsoluteValueFun v hc).add_le fun _ => bot_le

theorem valuationRing_iff_forall_mem_or_inv_mem
    (A : Type*) [CommRing A] [IsDomain A] :
    ValuationRing A ↔
      ∀ x : FractionRing A,
        IsLocalization.IsInteger A x ∨ IsLocalization.IsInteger A x⁻¹ :=
  ValuationRing.iff_isInteger_or_isInteger A (FractionRing A)

end
