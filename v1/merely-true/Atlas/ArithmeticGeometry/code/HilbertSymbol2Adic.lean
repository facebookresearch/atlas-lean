/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Hilbert2Adic
import Atlas.ArithmeticGeometry.code.Hilbert2AdicCore
import Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions

open PadicInt HilbertSymbol

noncomputable section

/-- The function $\varepsilon(u) = (u - 1) / 2 \pmod{2}$ applied to a $2$-adic unit $u$, computed
via its image in $(\mathbb{Z}/8\mathbb{Z})^\times$. -/
def epsilon_padic (u : ℤ_[2]ˣ) : ZMod 2 :=
  epsilon_ZMod8 (toZModPow_unit 3 u)

/-- The function $\omega(u) = (u^2 - 1) / 8 \pmod{2}$ applied to a $2$-adic unit $u$, computed
via its image in $(\mathbb{Z}/8\mathbb{Z})^\times$. -/
def omega_padic (u : ℤ_[2]ˣ) : ZMod 2 :=
  omega_ZMod8 (toZModPow_unit 3 u)

/-- The mod-$8$ primitive solution condition for type-one ($u x^2 + v y^2 \equiv z^2$) can be
checked using a decidable version on the images in $(\mathbb{Z}/8\mathbb{Z})^\times$. -/
lemma hasPrimSolMod8_one_eq (u v : ℤ_[2]ˣ) :
    HasPrimitiveSolutionMod8_one u v ↔
    hasPrimSolMod8_one_dec (toZModPow_unit 3 u) (toZModPow_unit 3 v) := by
  simp only [HasPrimitiveSolutionMod8_one, hasPrimSolMod8_one_dec, toZModPow_unit_coe]

/-- The mod-$8$ primitive solution condition for type-two (involving the factor $2$) can be
checked using a decidable version on the images in $(\mathbb{Z}/8\mathbb{Z})^\times$. -/
lemma hasPrimSolMod8_two_eq (u v : ℤ_[2]ˣ) :
    HasPrimitiveSolutionMod8_two u v ↔
    hasPrimSolMod8_two_dec (toZModPow_unit 3 u) (toZModPow_unit 3 v) := by
  simp only [HasPrimitiveSolutionMod8_two, hasPrimSolMod8_two_dec, toZModPow_unit_coe]

/-- Bridge between the abstract Hilbert symbol and a concrete formula $f \in \{1, -1\}$:
if the Hilbert symbol equals $1$ iff the form has a primitive solution, and the latter is
equivalent to a decidable mod-$8$ condition expressed by $f = 1$, then the Hilbert symbol
equals $f$. -/
lemma hilbert_eq_formula_of_iff
    {a b : ℚ_[2]ˣ}
    (h_iff : padicHilbertSymbol 2 a b = 1 ↔ HasPrimitiveSolution a b)
    {solMod : Prop} [Decidable solMod]
    (h_lift : HasPrimitiveSolution a b ↔ solMod)
    {f : ℤ} (hf : f = 1 ∨ f = -1)
    (h_formula : solMod ↔ f = 1) :
    padicHilbertSymbol 2 a b = f := by
  rcases padicHilbertSymbol.eq_one_or_neg_one a b with h | h
  · rw [h]
    rcases hf with hf1 | hf1
    · exact hf1.symm
    · exfalso
      have hsol : solMod := h_lift.mp (h_iff.mp h)
      rw [h_formula.mp hsol] at hf1; exact absurd hf1 (by omega)
  · rw [h]
    rcases hf with hf1 | hf1
    · exfalso
      have hf1' : f = 1 := hf1
      rw [← h_formula] at hf1'
      have := h_lift.mpr hf1'
      rw [← h_iff] at this
      rw [this] at h; exact absurd h (by omega)
    · exact hf1.symm

/-- The element $2 \in \mathbb{Q}_2^\times$, viewed as a unit. -/
noncomputable def twoQp : ℚ_[2]ˣ := (isUnit_of_invertible (2 : ℚ_[2])).unit

/-- The underlying value of the unit `twoQp` is $2$. -/
lemma twoQp_val : (twoQp : ℚ_[2]) = 2 := IsUnit.unit_spec _

/-- Decomposition of a "type-two" $2$-adic unit (of the form $2 \cdot v$) as the product
$2 \cdot v$. -/
lemma padicUnit_two_eq_mul (v : ℤ_[2]ˣ) :
    padicUnit_two v = twoQp * padicUnit_one v := by
  ext
  simp only [padicUnit_two_val, twoQp_val, padicUnit_one_val, Units.val_mul]

/-- Decomposition of a "type-two" $2$-adic unit as $u \cdot 2$ (commuted form). -/
lemma padicUnit_two_eq_mul' (u : ℤ_[2]ˣ) :
    padicUnit_two u = padicUnit_one u * twoQp := by
  ext
  simp only [padicUnit_two_val, twoQp_val, padicUnit_one_val, Units.val_mul, mul_comm]

/-- The unit $2 \in \mathbb{Q}_2^\times$ equals the type-two unit with multiplier $1$. -/
lemma twoQp_eq_padicUnit_two_one : twoQp = padicUnit_two 1 := by
  ext
  simp only [twoQp_val, padicUnit_two_val, Units.val_one]
  push_cast
  ring

/-- The element $-1 \in \mathbb{Q}_2^\times$ equals the type-one unit coming from
$-1 \in \mathbb{Z}_2^\times$. -/
lemma neg_one_eq_padicUnit_one : (-1 : ℚ_[2]ˣ) = padicUnit_one (-1 : ℤ_[2]ˣ) := by
  ext
  simp only [padicUnit_one_val, Units.val_neg, Units.val_one]
  push_cast
  ring

/-- The image of $1 \in \mathbb{Z}_2^\times$ under reduction to
$(\mathbb{Z}/8\mathbb{Z})^\times$ is $1$. -/
lemma toZModPow_unit_one : toZModPow_unit 3 (1 : ℤ_[2]ˣ) = 1 := by
  ext
  simp only [toZModPow_unit_coe, Units.val_one, map_one]

/-- The image of $-1 \in \mathbb{Z}_2^\times$ under reduction to
$(\mathbb{Z}/8\mathbb{Z})^\times$ is $-1$. -/
lemma toZModPow_unit_neg_one : toZModPow_unit 3 (-1 : ℤ_[2]ˣ) = -1 := by
  ext
  simp only [toZModPow_unit_coe, Units.val_neg, Units.val_one, map_neg, map_one]





end
