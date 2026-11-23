/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.HilbertSymbol

open PadicInt HilbertSymbol

/-- Reduction of a $2$-adic unit `u : ℤ_[2]ˣ` to a unit in `ZMod (2 ^ n)` via `toZModPow`. -/
noncomputable def toZModPow_unit (n : ℕ) (u : ℤ_[2]ˣ) : (ZMod (2 ^ n))ˣ :=
  (Units.isUnit u).map (toZModPow n : ℤ_[2] →+* ZMod (2 ^ n)) |>.unit

/-- The underlying element of `toZModPow_unit n u` agrees with `toZModPow n (↑u)`. -/
lemma toZModPow_unit_coe (n : ℕ) (u : ℤ_[2]ˣ) :
    (toZModPow_unit n u : ZMod (2 ^ n)) = toZModPow n (↑u) :=
  IsUnit.unit_spec _

/-- Decidable predicate: there exist `x₀, y₀, z₀ ∈ ZMod 8` with at least one a unit such
that $z_0^2 = u_0 x_0^2 + v_0 y_0^2$ (primitive solution mod $8$ for the case $\alpha = 0$). -/
@[reducible]
def hasPrimSolMod8_one_dec (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 + (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2

/-- Decidable predicate: there exist `x₀, y₀, z₀ ∈ ZMod 8` with at least one a unit such
that $z_0^2 = 2 u_0 x_0^2 + v_0 y_0^2$ (primitive solution mod $8$ for the case $\alpha = 1$). -/
@[reducible]
def hasPrimSolMod8_two_dec (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (2 : ZMod (2 ^ 3)) * (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 +
              (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2

instance (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Decidable (hasPrimSolMod8_one_dec u₀ v₀) :=
  inferInstance

instance (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Decidable (hasPrimSolMod8_two_dec u₀ v₀) :=
  inferInstance

/-- The invariant $\epsilon(u) = (u - 1)/2 \bmod 2$ for a unit `u` in `ZMod 8`. -/
def epsilon_ZMod8 (u : (ZMod (2 ^ 3))ˣ) : ZMod 2 :=
  ((((u : ZMod (2 ^ 3)).val - 1) / 2 : ℕ) : ZMod 2)

/-- The invariant $\omega(u) = (u^2 - 1)/8 \bmod 2$ for a unit `u` in `ZMod 8`. -/
def omega_ZMod8 (u : (ZMod (2 ^ 3))ˣ) : ZMod 2 :=
  ((((u : ZMod (2 ^ 3)).val ^ 2 - 1) / 8 : ℕ) : ZMod 2)

/-- The closed-form expression $(-1)^{\epsilon(u)\epsilon(v) + \alpha\omega(v) + \beta\omega(u)}$
for the $2$-adic Hilbert symbol on units (Theorem 10.9). -/
def hilbert2Adic_formula
    (u₀ v₀ : (ZMod (2 ^ 3))ˣ) (α β : ℕ) : ℤ :=
  (-1 : ℤ) ^ ((epsilon_ZMod8 u₀ * epsilon_ZMod8 v₀ +
    α * omega_ZMod8 v₀ + β * omega_ZMod8 u₀).val)





/-- The closed-form formula always evaluates to $\pm 1$, since it is a power of $-1$. -/
lemma formula_eq_one_or_neg_one (u₀ v₀ : (ZMod (2 ^ 3))ˣ) (α β : ℕ) :
    hilbert2Adic_formula u₀ v₀ α β = 1 ∨ hilbert2Adic_formula u₀ v₀ α β = -1 := by
  unfold hilbert2Adic_formula
  exact neg_one_pow_eq_or ℤ _

