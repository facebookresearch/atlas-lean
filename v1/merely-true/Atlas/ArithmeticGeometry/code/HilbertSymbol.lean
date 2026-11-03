/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Normed.Group.Ultra

open scoped Classical

namespace HilbertSymbol

section Defs

variable (F : Type*) [Field F]

/-- The equation $ax^2 + by^2 = 1$ has a solution $(x, y) \in F^2$. -/
def IsSolvable (a b : Fˣ) : Prop :=
  ∃ x y : F, (a : F) * x ^ 2 + (b : F) * y ^ 2 = 1

/-- The quadratic form $z^2 - ax^2 - by^2$ represents zero non-trivially over $F$,
i.e., $z^2 = ax^2 + by^2$ has a solution with $(x, y, z) \neq (0, 0, 0)$. -/
def RepresentsZero (a b : Fˣ) : Prop :=
  ∃ x y z : F, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ z ^ 2 = (a : F) * x ^ 2 + (b : F) * y ^ 2

/-- The unit $a \in F^\times$ is a norm from the quadratic extension $F(\sqrt{b})$,
i.e., there exist $z, y \in F$ with $z^2 - b y^2 = a$. -/
def IsNormFromSqrtExt (a b : Fˣ) : Prop :=
  ∃ z y : F, z ^ 2 - (b : F) * y ^ 2 = (a : F)

end Defs

section PadicDef

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The equation $ax^2 + by^2 = z^2$ admits a primitive $p$-adic integer solution,
i.e., one with $x, y, z \in \mathbb{Z}_p$ where at least one of them is a unit. -/
def HasPrimitiveSolution (a b : ℚ_[p]ˣ) : Prop :=
  ∃ x y z : ℤ_[p], (IsUnit x ∨ IsUnit y ∨ IsUnit z) ∧
    (a : ℚ_[p]) * (↑x : ℚ_[p]) ^ 2 + (b : ℚ_[p]) * (↑y : ℚ_[p]) ^ 2 = (↑z : ℚ_[p]) ^ 2

end PadicDef

end HilbertSymbol

variable (F : Type*) [Field F]

/-- The Hilbert symbol $(a, b)_F \in \{\pm 1\}$ for units of a field $F$:
takes the value $1$ if $ax^2 + by^2 = 1$ has a solution in $F$, and $-1$ otherwise.
This is Definition 10.1 of the textbook (in its general form for a field $F$). -/
noncomputable def hilbertSymbol (a b : Fˣ) : ℤ :=
  if HilbertSymbol.IsSolvable F a b then 1 else -1

namespace hilbertSymbol

variable {F : Type*} [Field F]

/-- $(a, b)_F = 1$ iff the equation $ax^2 + by^2 = 1$ is solvable in $F$. -/
@[simp]
lemma eq_one_iff {a b : Fˣ} :
    hilbertSymbol F a b = 1 ↔ HilbertSymbol.IsSolvable F a b := by
  unfold hilbertSymbol; split_ifs with h <;> simp_all

/-- $(a, b)_F = -1$ iff the equation $ax^2 + by^2 = 1$ is unsolvable in $F$. -/
lemma eq_neg_one_iff {a b : Fˣ} :
    hilbertSymbol F a b = -1 ↔ ¬HilbertSymbol.IsSolvable F a b := by
  unfold hilbertSymbol; split_ifs with h <;> simp_all

/-- The Hilbert symbol always takes the value $\pm 1$. -/
lemma eq_one_or_neg_one (a b : Fˣ) :
    hilbertSymbol F a b = 1 ∨ hilbertSymbol F a b = -1 := by
  unfold hilbertSymbol; split_ifs <;> simp

/-- $(a, b)_F^2 = 1$ since the Hilbert symbol is $\pm 1$. -/
lemma sq (a b : Fˣ) : hilbertSymbol F a b ^ 2 = 1 := by
  rcases eq_one_or_neg_one a b with h | h <;> simp [h]

/-- The Hilbert symbol is never zero. -/
lemma ne_zero (a b : Fˣ) : hilbertSymbol F a b ≠ 0 := by
  rcases eq_one_or_neg_one a b with h | h <;> simp [h]

end hilbertSymbol

/-- The $p$-adic Hilbert symbol $(a, b)_p$, defined as the Hilbert symbol over the
$p$-adic numbers $\mathbb{Q}_p$. -/
noncomputable def padicHilbertSymbol (p : ℕ) [Fact (Nat.Prime p)] (a b : ℚ_[p]ˣ) : ℤ :=
  hilbertSymbol ℚ_[p] a b

namespace padicHilbertSymbol

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- $(a, b)_p = 1$ iff the equation $ax^2 + by^2 = 1$ is solvable in $\mathbb{Q}_p$. -/
@[simp]
lemma eq_one_iff {a b : ℚ_[p]ˣ} :
    padicHilbertSymbol p a b = 1 ↔
      ∃ x y : ℚ_[p], (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 = 1 :=
  hilbertSymbol.eq_one_iff

/-- $(a, b)_p = -1$ iff the equation $ax^2 + by^2 = 1$ is unsolvable in $\mathbb{Q}_p$. -/
lemma eq_neg_one_iff {a b : ℚ_[p]ˣ} :
    padicHilbertSymbol p a b = -1 ↔
      ¬∃ x y : ℚ_[p], (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 = 1 :=
  hilbertSymbol.eq_neg_one_iff

/-- The $p$-adic Hilbert symbol takes values in $\{\pm 1\}$. -/
lemma eq_one_or_neg_one (a b : ℚ_[p]ˣ) :
    padicHilbertSymbol p a b = 1 ∨ padicHilbertSymbol p a b = -1 :=
  hilbertSymbol.eq_one_or_neg_one a b

/-- $(a, b)_p^2 = 1$. -/
lemma sq (a b : ℚ_[p]ˣ) : padicHilbertSymbol p a b ^ 2 = 1 :=
  hilbertSymbol.sq a b

/-- The $p$-adic Hilbert symbol is never zero. -/
lemma ne_zero (a b : ℚ_[p]ˣ) : padicHilbertSymbol p a b ≠ 0 :=
  hilbertSymbol.ne_zero a b

end padicHilbertSymbol

/-- The real Hilbert symbol $(a, b)_\infty$, defined as the Hilbert symbol over $\mathbb{R}$. -/
noncomputable def realHilbertSymbol (a b : ℝˣ) : ℤ :=
  hilbertSymbol ℝ a b

namespace realHilbertSymbol

/-- $(a, b)_\infty = 1$ iff the equation $ax^2 + by^2 = 1$ is solvable in $\mathbb{R}$. -/
@[simp]
lemma eq_one_iff {a b : ℝˣ} :
    realHilbertSymbol a b = 1 ↔ ∃ x y : ℝ, (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 = 1 :=
  hilbertSymbol.eq_one_iff

/-- $(a, b)_\infty = -1$ iff the equation $ax^2 + by^2 = 1$ is unsolvable in $\mathbb{R}$. -/
lemma eq_neg_one_iff {a b : ℝˣ} :
    realHilbertSymbol a b = -1 ↔
      ¬∃ x y : ℝ, (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 = 1 :=
  hilbertSymbol.eq_neg_one_iff

/-- The real Hilbert symbol takes values in $\{\pm 1\}$. -/
lemma eq_one_or_neg_one (a b : ℝˣ) :
    realHilbertSymbol a b = 1 ∨ realHilbertSymbol a b = -1 :=
  hilbertSymbol.eq_one_or_neg_one a b

/-- $(a, b)_\infty^2 = 1$. -/
lemma sq (a b : ℝˣ) : realHilbertSymbol a b ^ 2 = 1 :=
  hilbertSymbol.sq a b

/-- The real Hilbert symbol is never zero. -/
lemma ne_zero (a b : ℝˣ) : realHilbertSymbol a b ≠ 0 :=
  hilbertSymbol.ne_zero a b

/-- If $a > 0$, then $ax^2 + by^2 = 1$ is solvable over $\mathbb{R}$ (take $x = 1/\sqrt{a}$, $y = 0$). -/
lemma isSolvable_of_pos_left {a b : ℝˣ} (ha : (0 : ℝ) < (a : ℝ)) :
    HilbertSymbol.IsSolvable ℝ a b :=
  ⟨Real.sqrt ((a : ℝ)⁻¹), 0, by
    simp only [mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero]
    rw [_root_.sq, ← Real.sqrt_mul (inv_nonneg.mpr (le_of_lt ha)),
        Real.sqrt_mul_self (inv_nonneg.mpr (le_of_lt ha))]
    exact mul_inv_cancel₀ (ne_of_gt ha)⟩

/-- If $b > 0$, then $ax^2 + by^2 = 1$ is solvable over $\mathbb{R}$ (take $x = 0$, $y = 1/\sqrt{b}$). -/
lemma isSolvable_of_pos_right {a b : ℝˣ} (hb : (0 : ℝ) < (b : ℝ)) :
    HilbertSymbol.IsSolvable ℝ a b :=
  ⟨0, Real.sqrt ((b : ℝ)⁻¹), by
    simp only [mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_add]
    rw [_root_.sq, ← Real.sqrt_mul (inv_nonneg.mpr (le_of_lt hb)),
        Real.sqrt_mul_self (inv_nonneg.mpr (le_of_lt hb))]
    exact mul_inv_cancel₀ (ne_of_gt hb)⟩

/-- If both $a < 0$ and $b < 0$, then $ax^2 + by^2 \le 0 < 1$, so the equation
$ax^2 + by^2 = 1$ has no real solution. -/
lemma not_isSolvable_of_both_neg {a b : ℝˣ}
    (ha : (a : ℝ) < 0) (hb : (b : ℝ) < 0) :
    ¬HilbertSymbol.IsSolvable ℝ a b := by
  rintro ⟨x, y, hxy⟩
  have h1 : (a : ℝ) * x ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha) (sq_nonneg x)
  have h2 : (b : ℝ) * y ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_lt hb) (sq_nonneg y)
  linarith

/-- (Textbook Theorem 10.4, real case) The real Hilbert symbol satisfies
$(a, b)_\infty = -1$ if and only if both $a$ and $b$ are negative. -/
theorem eq_neg_one_iff_both_neg (a b : ℝˣ) :
    realHilbertSymbol a b = -1 ↔ (a : ℝ) < 0 ∧ (b : ℝ) < 0 := by
  rw [realHilbertSymbol, hilbertSymbol.eq_neg_one_iff]
  constructor
  · intro hns
    constructor
    · by_contra ha
      push Not at ha
      exact hns (isSolvable_of_pos_left (lt_of_le_of_ne ha (Ne.symm a.ne_zero)))
    · by_contra hb
      push Not at hb
      exact hns (isSolvable_of_pos_right (lt_of_le_of_ne hb (Ne.symm b.ne_zero)))
  · rintro ⟨ha, hb⟩
    exact not_isSolvable_of_both_neg ha hb

end realHilbertSymbol

namespace HilbertSymbol

section SolvableRepresentsZero

variable {F : Type*} [Field F] [CharZero F]

/-- Solvability of $ax^2 + by^2 = 1$ implies non-trivial representation of zero
by $z^2 - ax^2 - by^2$ (take $z = 1$). -/
lemma IsSolvable.representsZero {a b : Fˣ} (h : IsSolvable F a b) :
    RepresentsZero F a b := by
  obtain ⟨x₀, y₀, hxy⟩ := h
  exact ⟨x₀, y₀, 1, Or.inr (Or.inr one_ne_zero), by rw [one_pow]; exact hxy.symm⟩

omit [CharZero F] in
/-- Helper lemma: if $ax_0^2 + by_0^2 = 0$ and $x_0 \neq 0$, then $y_0 \neq 0$
(since otherwise $ax_0^2 = 0$, contradicting $a \neq 0$ and $x_0 \neq 0$). -/
lemma y_ne_zero_of_binary_zero {a b : Fˣ} {x₀ y₀ : F} (hx₀ : x₀ ≠ 0)
    (h0 : (a : F) * x₀ ^ 2 + (b : F) * y₀ ^ 2 = 0) : y₀ ≠ 0 := by
  intro hy
  rw [hy, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at h0
  rcases mul_eq_zero.mp h0 with ha | hx
  · exact a.ne_zero ha
  · exact hx₀ (pow_eq_zero_iff two_ne_zero |>.mp hx)

/-- Helper lemma: if the binary form $ax^2 + by^2$ represents zero non-trivially,
then it represents every element $c \in F$. -/
lemma binary_form_represents_all {a b : Fˣ} {x₀ y₀ : F} (hx₀ : x₀ ≠ 0)
    (h0 : (a : F) * x₀ ^ 2 + (b : F) * y₀ ^ 2 = 0) (c : F) :
    ∃ x y : F, (a : F) * x ^ 2 + (b : F) * y ^ 2 = c := by
  set α := y₀ / x₀
  have hα : α ≠ 0 := div_ne_zero (y_ne_zero_of_binary_zero hx₀ h0) hx₀
  have ha : (a : F) = -(b : F) * α ^ 2 := by
    have hx₀2 : x₀ ^ 2 ≠ 0 := pow_ne_zero 2 hx₀
    rw [div_pow,
      show -(b : F) * (y₀ ^ 2 / x₀ ^ 2) = -(b : F) * y₀ ^ 2 / x₀ ^ 2 from by ring,
      eq_div_iff hx₀2]
    linear_combination h0
  refine ⟨(c / (b : F) - 1) / (2 * α), (1 + c / (b : F)) / 2, ?_⟩
  rw [ha]; field_simp; ring

/-- If $z^2 - ax^2 - by^2$ represents zero non-trivially, then $ax^2 + by^2 = 1$ is solvable. -/
lemma RepresentsZero.isSolvable {a b : Fˣ} (h : RepresentsZero F a b) :
    IsSolvable F a b := by
  obtain ⟨x, y, z, hne, heq⟩ := h
  by_cases hz : z ≠ 0
  ·
    refine ⟨x / z, y / z, ?_⟩
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
    rw [div_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc, ← add_div,
      div_eq_one_iff_eq hz2]
    exact heq.symm
  ·
    push Not at hz; subst hz
    rw [zero_pow (by norm_num : 2 ≠ 0)] at heq
    have h0 : (a : F) * x ^ 2 + (b : F) * y ^ 2 = 0 := heq.symm
    have hx : x ≠ 0 := by
      rcases hne with hx | hy | hz'
      · exact hx
      · intro hx_eq
        rw [hx_eq, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] at h0
        rcases mul_eq_zero.mp h0 with hb | hy2
        · exact b.ne_zero hb
        · exact hy (pow_eq_zero_iff two_ne_zero |>.mp hy2)
      · exact absurd rfl hz'
    exact binary_form_represents_all hx h0 1

/-- (Textbook Lemma 10.2, parts (1) ↔ (2)) Solvability of $ax^2 + by^2 = 1$ over $F$ is
equivalent to non-trivial representation of zero by $z^2 - ax^2 - by^2$ over $F$. -/
theorem isSolvable_iff_representsZero {a b : Fˣ} :
    IsSolvable F a b ↔ RepresentsZero F a b :=
  ⟨IsSolvable.representsZero, RepresentsZero.isSolvable⟩

end SolvableRepresentsZero

section RepresentsZeroNorm

variable {F : Type*} [Field F] [CharZero F]

/-- If $a$ is a norm from $F(\sqrt{b})$, i.e., $z^2 - by^2 = a$ has a solution,
then $z^2 - ax^2 - by^2$ represents zero non-trivially (take $x = 1$). -/
lemma IsNormFromSqrtExt.representsZero {a b : Fˣ}
    (h : IsNormFromSqrtExt F a b) : RepresentsZero F a b := by
  obtain ⟨z, y, hzy⟩ := h
  refine ⟨1, y, z, Or.inl one_ne_zero, ?_⟩
  rw [one_pow, mul_one]; linear_combination hzy

/-- If $z^2 - ax^2 - by^2$ represents zero non-trivially, then $a$ is a norm
from the quadratic extension $F(\sqrt{b})$. -/
lemma RepresentsZero.isNormFromSqrtExt {a b : Fˣ}
    (h : RepresentsZero F a b) : IsNormFromSqrtExt F a b := by
  obtain ⟨x, y, z, hne, heq⟩ := h
  by_cases hx : x ≠ 0
  ·
    refine ⟨z / x, y / x, ?_⟩
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    field_simp; linear_combination heq
  ·
    push Not at hx; subst hx
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] at heq
    have hy : y ≠ 0 := by
      rcases hne with h1 | h2 | h3
      · exact absurd rfl h1
      · exact h2
      · intro hy_eq; rw [hy_eq, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at heq
        exact h3 (pow_eq_zero_iff two_ne_zero |>.mp heq)
    have hz : z ≠ 0 := by
      intro hz_eq; rw [hz_eq, zero_pow (by norm_num : 2 ≠ 0)] at heq
      rcases mul_eq_zero.mp heq.symm with hb | hy2
      · exact b.ne_zero hb
      · exact hy (pow_eq_zero_iff two_ne_zero |>.mp hy2)

    set γ := z / y
    have hγ : γ ≠ 0 := div_ne_zero hz hy
    have hb_eq : (b : F) = γ ^ 2 := by
      rw [div_pow, eq_div_iff (pow_ne_zero 2 hy)]; exact heq.symm
    refine ⟨((a : F) + 1) / 2, ((a : F) - 1) / (2 * γ), ?_⟩
    rw [hb_eq]; field_simp; ring

/-- (Textbook Lemma 10.2, parts (2) ↔ (3)) Non-trivial representation of zero by
$z^2 - ax^2 - by^2$ over $F$ is equivalent to $a$ being a norm from $F(\sqrt{b})$. -/
theorem representsZero_iff_isNormFromSqrtExt {a b : Fˣ} :
    RepresentsZero F a b ↔ IsNormFromSqrtExt F a b :=
  ⟨RepresentsZero.isNormFromSqrtExt, IsNormFromSqrtExt.representsZero⟩

end RepresentsZeroNorm

section RepresentsZeroPrimitive

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Helper: when $\|a\| \le \|b\|$, the quotient $a/b$ lies in $\mathbb{Z}_p$
(has $p$-adic norm $\le 1$). -/
noncomputable def toZpDiv {a b : ℚ_[p]} (h : ‖a‖ ≤ ‖b‖) : ℤ_[p] :=
  ⟨a / b, by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)⟩

/-- The underlying $\mathbb{Q}_p$-value of `toZpDiv h` is $a/b$. -/
@[simp]
lemma toZpDiv_coe {a b : ℚ_[p]} (h : ‖a‖ ≤ ‖b‖) :
    (↑(toZpDiv h) : ℚ_[p]) = a / b := rfl

/-- If $a \neq 0$ and $\|a\| \le \|b\|$, then $b \neq 0$. -/
lemma ne_zero_of_norm_le {a b : ℚ_[p]} (ha : a ≠ 0) (h : ‖a‖ ≤ ‖b‖) : b ≠ 0 := by
  intro hb; rw [hb, norm_zero] at h
  exact absurd h (not_le.mpr (norm_pos_iff.mpr ha))

/-- Among three elements of $\mathbb{Q}_p$ not all zero, one of them has maximum
$p$-adic norm (and is non-zero); used to extract a primitive representative. -/
lemma exists_max_norm {x y z : ℚ_[p]} (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    (‖y‖ ≤ ‖x‖ ∧ ‖z‖ ≤ ‖x‖ ∧ x ≠ 0) ∨
    (‖x‖ ≤ ‖y‖ ∧ ‖z‖ ≤ ‖y‖ ∧ y ≠ 0) ∨
    (‖x‖ ≤ ‖z‖ ∧ ‖y‖ ≤ ‖z‖ ∧ z ≠ 0) := by
  by_cases hxy : ‖x‖ ≤ ‖y‖
  · by_cases hyz : ‖y‖ ≤ ‖z‖
    · right; right
      exact ⟨le_trans hxy hyz, hyz,
        hne.elim (ne_zero_of_norm_le · (le_trans hxy hyz))
          (·.elim (ne_zero_of_norm_le · hyz) id)⟩
    · right; left
      push Not at hyz
      exact ⟨hxy, le_of_lt hyz,
        hne.elim (ne_zero_of_norm_le · hxy)
          (·.elim id (ne_zero_of_norm_le · (le_of_lt hyz)))⟩
  · push Not at hxy
    by_cases hxz : ‖x‖ ≤ ‖z‖
    · right; right
      exact ⟨hxz, le_trans (le_of_lt hxy) hxz,
        hne.elim (ne_zero_of_norm_le · hxz)
          (·.elim (ne_zero_of_norm_le · (le_trans (le_of_lt hxy) hxz)) id)⟩
    · left
      push Not at hxz
      exact ⟨le_of_lt hxy, le_of_lt hxz,
        hne.elim id
          (·.elim (ne_zero_of_norm_le · (le_of_lt hxy))
            (ne_zero_of_norm_le · (le_of_lt hxz)))⟩

/-- Constructs a primitive $p$-adic integer solution when $x$ has maximum norm
(rescaling by dividing through by $x$). -/
lemma primitive_of_x_max {a b : ℚ_[p]ˣ} {x y z : ℚ_[p]}
    (hx : x ≠ 0) (hyx : ‖y‖ ≤ ‖x‖) (hzx : ‖z‖ ≤ ‖x‖)
    (heq : z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) :
    HasPrimitiveSolution a b := by
  refine ⟨1, toZpDiv hyx, toZpDiv hzx, Or.inl isUnit_one, ?_⟩
  simp only [toZpDiv_coe, PadicInt.coe_one, one_pow, mul_one, div_pow]
  rw [show (a : ℚ_[p]) + (b : ℚ_[p]) * (y ^ 2 / x ^ 2) =
    ((a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) / x ^ 2 from by field_simp, heq]

/-- Constructs a primitive $p$-adic integer solution when $y$ has maximum norm. -/
lemma primitive_of_y_max {a b : ℚ_[p]ˣ} {x y z : ℚ_[p]}
    (hy : y ≠ 0) (hxy : ‖x‖ ≤ ‖y‖) (hzy : ‖z‖ ≤ ‖y‖)
    (heq : z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) :
    HasPrimitiveSolution a b := by
  refine ⟨toZpDiv hxy, 1, toZpDiv hzy, Or.inr (Or.inl isUnit_one), ?_⟩
  simp only [toZpDiv_coe, PadicInt.coe_one, one_pow, mul_one, div_pow]
  rw [show (a : ℚ_[p]) * (x ^ 2 / y ^ 2) + (b : ℚ_[p]) =
    ((a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) / y ^ 2 from by field_simp, heq]

/-- Constructs a primitive $p$-adic integer solution when $z$ has maximum norm. -/
lemma primitive_of_z_max {a b : ℚ_[p]ˣ} {x y z : ℚ_[p]}
    (hz : z ≠ 0) (hxz : ‖x‖ ≤ ‖z‖) (hyz : ‖y‖ ≤ ‖z‖)
    (heq : z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) :
    HasPrimitiveSolution a b := by
  refine ⟨toZpDiv hxz, toZpDiv hyz, 1, Or.inr (Or.inr isUnit_one), ?_⟩
  simp only [toZpDiv_coe, PadicInt.coe_one, one_pow, div_pow]
  rw [show (a : ℚ_[p]) * (x ^ 2 / z ^ 2) + (b : ℚ_[p]) * (y ^ 2 / z ^ 2) =
    ((a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) / z ^ 2 from by field_simp,
    ← heq, div_self (pow_ne_zero 2 hz)]

/-- Over $\mathbb{Q}_p$, non-trivial representation of zero by $z^2 - ax^2 - by^2$
implies the existence of a primitive $p$-adic integer solution. -/
lemma RepresentsZero.hasPrimitiveSolution {a b : ℚ_[p]ˣ}
    (h : RepresentsZero ℚ_[p] a b) : HasPrimitiveSolution a b := by
  obtain ⟨x, y, z, hne, heq⟩ := h
  rcases exists_max_norm hne with ⟨hyx, hzx, hx⟩ | ⟨hxy, hzy, hy⟩ | ⟨hxz, hyz, hz⟩
  · exact primitive_of_x_max hx hyx hzx heq
  · exact primitive_of_y_max hy hxy hzy heq
  · exact primitive_of_z_max hz hxz hyz heq

/-- A primitive $p$-adic integer solution immediately gives non-trivial
representation of zero over $\mathbb{Q}_p$. -/
lemma HasPrimitiveSolution.representsZero {a b : ℚ_[p]ˣ}
    (h : HasPrimitiveSolution a b) : RepresentsZero ℚ_[p] a b := by
  obtain ⟨x, y, z, hunit, heq⟩ := h
  refine ⟨↑x, ↑y, ↑z, ?_, heq.symm⟩
  rcases hunit with hu | hu | hu
  · left; exact PadicInt.coe_ne_zero.mpr hu.ne_zero
  · right; left; exact PadicInt.coe_ne_zero.mpr hu.ne_zero
  · right; right; exact PadicInt.coe_ne_zero.mpr hu.ne_zero

/-- (Textbook Lemma 10.2, parts (2) ↔ (4)) Over $\mathbb{Q}_p$, non-trivial representation
of zero is equivalent to existence of a primitive $p$-adic integer solution. -/
theorem representsZero_iff_hasPrimitiveSolution {a b : ℚ_[p]ˣ} :
    RepresentsZero ℚ_[p] a b ↔ HasPrimitiveSolution a b :=
  ⟨RepresentsZero.hasPrimitiveSolution, HasPrimitiveSolution.representsZero⟩

end RepresentsZeroPrimitive

section Lemma102

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- (Textbook Lemma 10.2, parts (1) ↔ (2) over $\mathbb{Q}_p$) Solvability of
$ax^2 + by^2 = 1$ over $\mathbb{Q}_p$ is equivalent to representation of zero. -/
theorem lemma_10_2 (a b : ℚ_[p]ˣ) :
    IsSolvable ℚ_[p] a b ↔ RepresentsZero ℚ_[p] a b := isSolvable_iff_representsZero

/-- (Textbook Lemma 10.2, parts (1) ↔ (4)) Solvability of $ax^2 + by^2 = 1$ over
$\mathbb{Q}_p$ is equivalent to existence of a primitive $p$-adic integer solution. -/
theorem isSolvable_iff_hasPrimitiveSolution (a b : ℚ_[p]ˣ) :
    IsSolvable ℚ_[p] a b ↔ HasPrimitiveSolution a b := by
  rw [isSolvable_iff_representsZero, representsZero_iff_hasPrimitiveSolution]

/-- (Textbook Lemma 10.2, parts (1) ↔ (3)) Solvability of $ax^2 + by^2 = 1$ over
$\mathbb{Q}_p$ is equivalent to $a$ being a norm from $\mathbb{Q}_p(\sqrt{b})$. -/
theorem isSolvable_iff_isNormFromSqrtExt (a b : ℚ_[p]ˣ) :
    IsSolvable ℚ_[p] a b ↔ IsNormFromSqrtExt ℚ_[p] a b := by
  rw [isSolvable_iff_representsZero, representsZero_iff_isNormFromSqrtExt]

/-- (Textbook Lemma 10.2, parts (3) ↔ (4)) Over $\mathbb{Q}_p$, existence of a primitive
solution is equivalent to $a$ being a norm from $\mathbb{Q}_p(\sqrt{b})$. -/
theorem hasPrimitiveSolution_iff_isNormFromSqrtExt (a b : ℚ_[p]ˣ) :
    HasPrimitiveSolution a b ↔ IsNormFromSqrtExt ℚ_[p] a b := by
  rw [← representsZero_iff_hasPrimitiveSolution, representsZero_iff_isNormFromSqrtExt]

/-- The $p$-adic Hilbert symbol is $1$ iff $z^2 - ax^2 - by^2$ represents zero non-trivially. -/
theorem hilbert_eq_one_iff_representsZero (a b : ℚ_[p]ˣ) :
    padicHilbertSymbol p a b = 1 ↔ RepresentsZero ℚ_[p] a b := by
  rw [padicHilbertSymbol.eq_one_iff]; exact isSolvable_iff_representsZero

/-- The $p$-adic Hilbert symbol is $1$ iff there exists a primitive
$p$-adic integer solution. -/
theorem hilbert_eq_one_iff_hasPrimitiveSolution (a b : ℚ_[p]ˣ) :
    padicHilbertSymbol p a b = 1 ↔ HasPrimitiveSolution a b := by
  rw [padicHilbertSymbol.eq_one_iff]; exact isSolvable_iff_hasPrimitiveSolution a b

/-- The $p$-adic Hilbert symbol is $1$ iff $a$ is a norm from $\mathbb{Q}_p(\sqrt{b})$. -/
theorem hilbert_eq_one_iff_isNormFromSqrtExt (a b : ℚ_[p]ˣ) :
    padicHilbertSymbol p a b = 1 ↔ IsNormFromSqrtExt ℚ_[p] a b := by
  rw [padicHilbertSymbol.eq_one_iff]; exact isSolvable_iff_isNormFromSqrtExt a b

end Lemma102

end HilbertSymbol

namespace hilbertSymbol

variable {F : Type*} [Field F]


section Cor103

variable [CharZero F]

/-- (Textbook Corollary 10.3, part 1) For any unit $c \in F^\times$,
$(-c, c)_F = 1$, since $(-c) \cdot ((c^{-1}-1)/2)^2 + c \cdot ((1+c^{-1})/2)^2 = 1$. -/
theorem hilbert_neg_self (c : Fˣ) : hilbertSymbol F (-c) c = 1 := by
  rw [eq_one_iff]
  refine ⟨((c : F)⁻¹ - 1) / 2, (1 + (c : F)⁻¹) / 2, ?_⟩
  have hc : (c : F) ≠ 0 := c.ne_zero
  simp only [Units.val_neg]
  field_simp
  ring

omit [CharZero F] in
/-- The set of norms from $F(\sqrt{c})$ is closed under multiplication. -/
lemma isNormFromSqrtExt_mul {a b c : Fˣ}
    (ha : HilbertSymbol.IsNormFromSqrtExt F a c)
    (hb : HilbertSymbol.IsNormFromSqrtExt F b c) :
    HilbertSymbol.IsNormFromSqrtExt F (a * b) c := by
  obtain ⟨z₀, w₀, h₀⟩ := ha
  obtain ⟨z₁, w₁, h₁⟩ := hb
  refine ⟨z₀ * z₁ + (c : F) * w₀ * w₁, z₀ * w₁ + z₁ * w₀, ?_⟩
  simp only [Units.val_mul]
  linear_combination (z₁ ^ 2 - ↑c * w₁ ^ 2) * h₀ + (↑a : F) * h₁

/-- If both $ax^2 + cy^2 = 1$ and $bx^2 + cy^2 = 1$ are solvable, then so is
$(ab)x^2 + cy^2 = 1$. This is the multiplicativity in the first argument
when the symbol equals $1$. -/
lemma isSolvable_mul_of_isSolvable {a b c : Fˣ}
    (ha : HilbertSymbol.IsSolvable F a c)
    (hb : HilbertSymbol.IsSolvable F b c) :
    HilbertSymbol.IsSolvable F (a * b) c := by
  rw [HilbertSymbol.isSolvable_iff_representsZero,
      HilbertSymbol.representsZero_iff_isNormFromSqrtExt]
  exact isNormFromSqrtExt_mul
    ((HilbertSymbol.isSolvable_iff_representsZero.mp ha |>
      HilbertSymbol.representsZero_iff_isNormFromSqrtExt.mp))
    ((HilbertSymbol.isSolvable_iff_representsZero.mp hb |>
      HilbertSymbol.representsZero_iff_isNormFromSqrtExt.mp))

omit [CharZero F] in
/-- If $ax^2 + cy^2 = 1$ is solvable, then so is $a^{-1}x^2 + cy^2 = 1$
(using the substitution $x \mapsto ax$). -/
lemma isSolvable_inv_of_isSolvable {a c : Fˣ}
    (h : HilbertSymbol.IsSolvable F a c) : HilbertSymbol.IsSolvable F a⁻¹ c := by
  obtain ⟨x₀, y₀, hxy⟩ := h
  refine ⟨(a : F) * x₀, y₀, ?_⟩
  simp only [Units.val_inv_eq_inv_val, mul_pow]
  have : (↑a : F)⁻¹ * ((↑a : F) ^ 2 * x₀ ^ 2) = ↑a * x₀ ^ 2 := by field_simp
  rw [this]; exact hxy

/-- Bilinearity in the first argument when $(a, c)_F = 1$: in that case,
$(a, c)_F \cdot (b, c)_F = (ab, c)_F$. -/
theorem hilbert_mul_of_eq_one (a b c : Fˣ) (h : hilbertSymbol F a c = 1) :
    hilbertSymbol F a c * hilbertSymbol F b c = hilbertSymbol F (a * b) c := by
  rw [h, one_mul]
  have ha : HilbertSymbol.IsSolvable F a c := eq_one_iff.mp h
  rcases eq_one_or_neg_one b c with hb | hb <;>
    rcases eq_one_or_neg_one (a * b) c with hab | hab
  · rw [hb, hab]
  · exfalso
    exact eq_neg_one_iff.mp hab (isSolvable_mul_of_isSolvable ha (eq_one_iff.mp hb))
  · exfalso
    have habs := eq_one_iff.mp hab
    have hbs := isSolvable_mul_of_isSolvable (isSolvable_inv_of_isSolvable ha) habs
    rw [show (a⁻¹ * (a * b) : Fˣ) = b from by simp] at hbs
    exact eq_neg_one_iff.mp hb hbs
  · rw [hb, hab]

/-- (Textbook Corollary 10.3, part 2) For any unit $c \in F^\times$,
$(c, c)_F = (-1, c)_F$. -/
theorem hilbert_self_eq_neg_one (c : Fˣ) :
    hilbertSymbol F c c = hilbertSymbol F (-1) c := by
  have h_neg_c : hilbertSymbol F (-c) c = 1 := hilbert_neg_self c
  have key := hilbert_mul_of_eq_one (-c) (-1) c h_neg_c
  simp only [h_neg_c, one_mul] at key
  rw [show ((-c) * (-1) : Fˣ) = c from by ext; simp] at key
  exact key.symm

end Cor103

end hilbertSymbol

namespace HilbertSymbol

/-- Inclusion of $p$-adic integer units into $p$-adic field units: $\mathbb{Z}_p^\times
\hookrightarrow \mathbb{Q}_p^\times$. -/
noncomputable def unitZpToQp {p : ℕ} [Fact (Nat.Prime p)] (u : ℤ_[p]ˣ) : ℚ_[p]ˣ :=
  Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom u

/-- The image of `unitZpToQp u` in $\mathbb{Q}_p$ agrees with the inclusion of $u$. -/
lemma unitZpToQp_coe {p : ℕ} [Fact (Nat.Prime p)] (u : ℤ_[p]ˣ) :
    (unitZpToQp u : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) := by
  simp [unitZpToQp, Units.coe_map]

set_option maxHeartbeats 800000 in
open Polynomial in
/-- (Helper, key step of Lemma 10.5) For odd prime $p$ and $p$-adic integer units
$u, v \in \mathbb{Z}_p^\times$, there exist $x_0, y_0 \in \mathbb{Z}_p$ and a unit
$z_0 \in \mathbb{Z}_p^\times$ such that $z_0^2 = u x_0^2 + v y_0^2$. The proof uses
Chevalley–Warning to find a solution modulo $p$, then Hensel's lemma to lift it. -/
theorem chevalley_warning_hensel_lift
    (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2) (u v : ℤ_[p]ˣ) :
    ∃ (x₀ y₀ : ℤ_[p]) (z₀ : ℤ_[p]ˣ),
      (z₀ : ℤ_[p]) ^ 2 = (u : ℤ_[p]) * x₀ ^ 2 + (v : ℤ_[p]) * y₀ ^ 2 := by
  have hp := Fact.out (p := Nat.Prime p)

  have hu_unit : IsUnit (PadicInt.toZMod (u : ℤ_[p])) :=
    RingHom.isUnit_map PadicInt.toZMod u.isUnit
  have hv_unit : IsUnit (PadicInt.toZMod (v : ℤ_[p])) :=
    RingHom.isUnit_map PadicInt.toZMod v.isUnit
  set u_bar := hu_unit.unit
  set v_bar := hv_unit.unit
  have hu_bar_val : (u_bar : ZMod p) = PadicInt.toZMod (u : ℤ_[p]) := by
    simp [u_bar, IsUnit.unit_spec]
  have hv_bar_val : (v_bar : ZMod p) = PadicInt.toZMod (v : ℤ_[p]) := by
    simp [v_bar, IsUnit.unit_spec]

  open Polynomial in
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card p]
    exact Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp hp_odd)
  have hu_ne : (u_bar : ZMod p) ≠ 0 := Units.ne_zero _
  have hv_ne : (v_bar : ZMod p) ≠ 0 := Units.ne_zero _
  open Polynomial in
  have hf : (C (u_bar : ZMod p) * X ^ 2 - C 1).degree = 2 := by
    rw [degree_sub_eq_left_of_degree_lt]
    · simp [degree_C_mul_X_pow 2 hu_ne]
    · rw [degree_C_mul_X_pow 2 hu_ne]; simp
  open Polynomial in
  have hg : (C (v_bar : ZMod p) * X ^ 2).degree = 2 := by
    simp [degree_C_mul_X_pow 2 hv_ne]
  open Polynomial in
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
  open Polynomial in
  have hab' : (u_bar : ZMod p) * a ^ 2 + (v_bar : ZMod p) * b ^ 2 = 1 := by
    have : (u_bar : ZMod p) * a ^ 2 - 1 + (v_bar : ZMod p) * b ^ 2 = 0 := by
      convert hab using 1
      simp [eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination this

  obtain ⟨a_lift, ha_lift⟩ := ZMod.ringHom_surjective PadicInt.toZMod a
  obtain ⟨b_lift, hb_lift⟩ := ZMod.ringHom_surjective PadicInt.toZMod b

  set c := (u : ℤ_[p]) * a_lift ^ 2 + (v : ℤ_[p]) * b_lift ^ 2 with hc_def
  have hc_mod : PadicInt.toZMod c = 1 := by
    simp only [hc_def, map_add, map_mul, map_pow, ha_lift, hb_lift,
               ← hu_bar_val, ← hv_bar_val]
    exact hab'

  have hnorm_1_sub_c : ‖(1 : ℤ_[p]) - c‖ < 1 := by
    have hmem : (1 - c) ∈ RingHom.ker PadicInt.toZMod :=
      show PadicInt.toZMod (1 - c) = 0 by simp [map_sub, map_one, hc_mod]
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
        Ideal.mem_span_singleton] at hmem
    exact (PadicInt.norm_lt_one_iff_dvd _).2 hmem

  have hnorm_two : ‖(2 : ℤ_[p])‖ = 1 := by
    have h1 : ‖(2 : ℤ_[p])‖ ≤ 1 := PadicInt.norm_le_one _
    have h2 : ¬ (‖(2 : ℤ_[p])‖ < 1) := by
      rw [show (2 : ℤ_[p]) = ((2 : ℤ) : ℤ_[p]) from by push_cast; ring]
      rw [PadicInt.norm_int_lt_one_iff_dvd]
      intro hdvd
      have h3 : p ∣ 2 := by exact_mod_cast hdvd
      have h4 := Nat.le_of_dvd (by norm_num) h3
      have h5 := hp.two_le
      omega
    linarith

  open Polynomial in
  have h_aeval : Polynomial.aeval (1 : ℤ_[p]) (X ^ 2 - C c : Polynomial ℤ_[p]) = 1 - c := by
    simp [aeval_def]
  open Polynomial in
  have h_deriv : Polynomial.aeval (1 : ℤ_[p])
      (Polynomial.derivative (X ^ 2 - C c : Polynomial ℤ_[p])) = 2 := by
    simp [derivative_sub, derivative_pow, derivative_C, derivative_X, aeval_def]
  open Polynomial in
  have hensel_hyp : ‖Polynomial.aeval (1 : ℤ_[p]) (X ^ 2 - C c : Polynomial ℤ_[p])‖ <
      ‖Polynomial.aeval (1 : ℤ_[p])
        (Polynomial.derivative (X ^ 2 - C c : Polynomial ℤ_[p]))‖ ^ 2 := by
    rw [h_aeval, h_deriv, hnorm_two, one_pow]
    exact hnorm_1_sub_c
  open Polynomial in
  obtain ⟨z₀, hz₀_eval, hz₀_close, _, _⟩ := hensels_lemma hensel_hyp

  open Polynomial in
  have hz₀_sq : z₀ ^ 2 = c := by
    simp [aeval_def] at hz₀_eval
    linear_combination hz₀_eval

  open Polynomial in
  have hz₀_close' : ‖z₀ - 1‖ < 1 := by
    have : ‖z₀ - 1‖ < ‖Polynomial.aeval (1 : ℤ_[p])
        (Polynomial.derivative (X ^ 2 - C c : Polynomial ℤ_[p]))‖ := hz₀_close
    rw [h_deriv, hnorm_two] at this
    exact this
  have hz₀_unit : IsUnit z₀ := by
    rw [PadicInt.isUnit_iff]
    have h1 : ‖(1 : ℤ_[p])‖ = 1 := by simp
    have hne : ‖z₀ - 1‖ ≠ ‖(1 : ℤ_[p])‖ := by
      rw [h1]; exact ne_of_lt hz₀_close'
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
    rw [sub_add_cancel] at this
    rw [this, h1, max_eq_right (le_of_lt hz₀_close')]

  refine ⟨a_lift, b_lift, hz₀_unit.unit, ?_⟩
  rw [IsUnit.unit_spec, hz₀_sq]

/-- (Textbook Lemma 10.5) For an odd prime $p$ and any two $p$-adic integer units
$u, v \in \mathbb{Z}_p^\times$, the Hilbert symbol $(u, v)_p = 1$. -/
theorem hilbert_symbol_units_eq_one_of_odd
    (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2) (u v : ℤ_[p]ˣ) :
    padicHilbertSymbol p (unitZpToQp u) (unitZpToQp v) = 1 := by
  rw [padicHilbertSymbol.eq_one_iff]
  obtain ⟨x₀, y₀, z₀, hz⟩ := chevalley_warning_hensel_lift p hp_odd u v

  have hz_qp : ((z₀ : ℤ_[p]) : ℚ_[p]) ^ 2 =
      ((u : ℤ_[p]) : ℚ_[p]) * ((x₀ : ℚ_[p])) ^ 2 +
      ((v : ℤ_[p]) : ℚ_[p]) * ((y₀ : ℚ_[p])) ^ 2 := by
    have := congrArg (PadicInt.Coe.ringHom (p := p)) hz
    simp only [map_pow, map_mul, map_add] at this
    exact this
  have hz_ne : ((z₀ : ℤ_[p]) : ℚ_[p]) ≠ 0 := by simp [z₀.ne_zero]

  refine ⟨↑x₀ / ↑(z₀ : ℤ_[p]), ↑y₀ / ↑(z₀ : ℤ_[p]), ?_⟩
  rw [unitZpToQp_coe, unitZpToQp_coe,
      div_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc, ← add_div,
      div_eq_one_iff_eq (pow_ne_zero 2 hz_ne)]
  exact hz_qp.symm

end HilbertSymbol
