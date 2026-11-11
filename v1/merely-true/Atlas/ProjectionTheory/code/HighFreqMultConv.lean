/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.LinnikLargeSieve
import Atlas.ProjectionTheory.code.MultiplicativeConvolution

open Finset Complex BigOperators

noncomputable section

namespace HighFreqMultConv

variable (q : ℕ) [NeZero q]

/-- The *multiplicative convolution* on the group of units `(ZMod q)ˣ`:
$(f *_M g)(a) = \sum_{b \in (\mathbb{Z}/q)^\times} f(b)\, g(a/b)$. -/
def mulConvUnits (f g : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) : ℂ :=
  ∑ b : (ZMod q)ˣ, f b * g (a / b)

/-- The *high-frequency part* `f_h = f - f₀` of a function on `(ZMod q)ˣ`, where `f₀`
is the constant function equal to the average $\langle f \rangle = \frac{1}{|(\mathbb{Z}/q)^\times|}\sum_b f(b)$. -/
def highFreqUnits (f : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) : ℂ :=
  f a - (∑ b : (ZMod q)ˣ, f b) / (Fintype.card (ZMod q)ˣ : ℂ)

/-- Translation invariance from the left: summing `g(a/b)` over `b` gives the same answer
as summing `g(b)` over `b`, since `b ↦ a/b` is a bijection of `(ZMod q)ˣ`. -/
lemma sum_div_left_eq (g : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) :
    ∑ b : (ZMod q)ˣ, g (a / b) = ∑ b : (ZMod q)ˣ, g b :=
  Fintype.sum_equiv (Equiv.divLeft a) _ _ (fun _ => rfl)

/-- Translation invariance from the right: summing `g(i/x)` over `i` equals `∑ g(i)`. -/
lemma sum_div_right_eq (g : (ZMod q)ˣ → ℂ) (x : (ZMod q)ˣ) :
    ∑ i : (ZMod q)ˣ, g (i / x) = ∑ i : (ZMod q)ˣ, g i :=
  Fintype.sum_equiv (Equiv.divRight x) _ _ (fun _ => rfl)

/-- **High-frequency part of a multiplicative convolution** (Lemma 4 in Section 7.3).
On `(ZMod q)ˣ`, taking the high-frequency part commutes with multiplicative convolution:
$(f^* *_M g^*)_h = f^*_h *_M g^*_h$. -/
theorem highFreq_mulConvUnits [Fact (Nat.Prime q)]
    (f g : (ZMod q)ˣ → ℂ) :
    highFreqUnits q (mulConvUnits q f g) =
      mulConvUnits q (highFreqUnits q f) (highFreqUnits q g) := by
  funext a
  simp only [highFreqUnits, mulConvUnits]
  have hn : (Fintype.card (ZMod q)ˣ : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hga : ∑ b : (ZMod q)ˣ, g (a / b) = ∑ b : (ZMod q)ˣ, g b :=
    sum_div_left_eq q g a
  have hconv : (∑ c : (ZMod q)ˣ, ∑ b : (ZMod q)ˣ, f b * g (c / b)) =
      (∑ b : (ZMod q)ˣ, f b) * (∑ b : (ZMod q)ˣ, g b) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_div_right_eq]
    rw [← Finset.sum_mul]
  rw [hconv]
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, hga, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp_rw [← Finset.sum_mul]
  field_simp
  ring

end HighFreqMultConv
