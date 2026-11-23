/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.LinearCombination
import Atlas.ArithmeticGeometry.code.HilbertSymbol

open Polynomial PadicInt HilbertSymbol

noncomputable section

/-- The reduction map $\mathbb{Z}_p \to \mathbb{Z}/p^n\mathbb{Z}$ is surjective. -/
lemma PadicInt.toZModPow_surjective' {p : ℕ} [Fact (Nat.Prime p)] (n : ℕ) :
    Function.Surjective (toZModPow n : ℤ_[p] →+* ZMod (p ^ n)) := by
  intro x
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective x
  exact ⟨k, by rw [map_intCast, hk]⟩

/-- An element of $\mathbb{Z}_p$ reduces to zero mod $p^n$ iff it is divisible by $p^n$. -/
lemma PadicInt.toZModPow_eq_zero_iff_dvd {p : ℕ} [Fact (Nat.Prime p)] (n : ℕ) (x : ℤ_[p]) :
    toZModPow n x = 0 ↔ (p : ℤ_[p]) ^ n ∣ x := by
  rw [← RingHom.mem_ker, ker_toZModPow, Ideal.mem_span_singleton]

/-- For $n \geq 1$, an element of $\mathbb{Z}_p$ is a unit iff its reduction mod $p^n$
is a unit. -/
lemma PadicInt.isUnit_toZModPow_iff {p : ℕ} [hp : Fact (Nat.Prime p)]
    {n : ℕ} (hn : 0 < n) {x : ℤ_[p]} :
    IsUnit (toZModPow n x) ↔ IsUnit x := by
  constructor
  · intro h
    rw [isUnit_iff]
    by_contra hne
    have hlt : ‖x‖ < 1 := lt_of_le_of_ne (norm_le_one x) hne
    rw [PadicInt.norm_lt_one_iff_dvd] at hlt
    have h1 : toZModPow 1 x = 0 := by
      rw [← RingHom.mem_ker, ker_toZModPow, Ideal.mem_span_singleton, pow_one]
      exact hlt
    have hcomp := congr_fun (congr_arg DFunLike.coe (zmod_cast_comp_toZModPow 1 n hn)) x
    simp only [RingHom.comp_apply] at hcomp
    rw [h1] at hcomp
    have hu : IsUnit ((ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 1))) (toZModPow n x)) :=
      h.map _
    rw [hcomp] at hu
    haveI : Nontrivial (ZMod (p ^ 1)) := by
      rw [show p ^ 1 = p from pow_one p]
      haveI : NeZero p := ⟨hp.out.ne_zero⟩
      infer_instance
    exact not_isUnit_zero hu
  · exact fun h => h.map (toZModPow n)

/-- Primitive mod-$8$ solvability of $z^2 = u x^2 + v y^2$ over $\mathbb{Z}_2$: there exist
$x_0, y_0, z_0 \in \mathbb{Z}/8\mathbb{Z}$, not all non-units, satisfying the equation. -/
def HasPrimitiveSolutionMod8_one (u v : ℤ_[2]ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (PadicInt.toZModPow 3 (↑u)) * x₀ ^ 2 + (PadicInt.toZModPow 3 (↑v)) * y₀ ^ 2

/-- Primitive mod-$8$ solvability of $z^2 = 2u x^2 + v y^2$ over $\mathbb{Z}_2$. -/
def HasPrimitiveSolutionMod8_two (u v : ℤ_[2]ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (2 : ZMod (2 ^ 3)) * (PadicInt.toZModPow 3 (↑u)) * x₀ ^ 2 +
              (PadicInt.toZModPow 3 (↑v)) * y₀ ^ 2

/-- Lift of a $\mathbb{Z}_2$-unit to a $\mathbb{Q}_2$-unit (i.e. multiplication by $1$). -/
noncomputable def padicUnit_one (u : ℤ_[2]ˣ) : ℚ_[2]ˣ :=
  ((Units.isUnit u).map (algebraMap ℤ_[2] ℚ_[2])).unit

/-- The $\mathbb{Q}_2$-unit $2u$ obtained by multiplying the lift of `u` by $2$. -/
noncomputable def padicUnit_two (u : ℤ_[2]ˣ) : ℚ_[2]ˣ :=
  ((isUnit_of_invertible (2 : ℚ_[2])).mul
    ((Units.isUnit u).map (algebraMap ℤ_[2] ℚ_[2]))).unit

/-- The $2$-adic norm of $2$ equals $1/2$. -/
lemma norm_two_padic : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
  rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) from rfl]
  exact_mod_cast @PadicInt.norm_p 2 (Fact.mk Nat.prime_two)

/-- Hensel-lifting consequence: if $a$ is a unit, $z$ is a unit, and $az^2 \equiv c \pmod 8$,
then there exists a unit $z'$ with $a (z')^2 = c$ exactly. -/
lemma exists_mul_sq_eq_of_mod8 {a c z : ℤ_[2]} (ha : IsUnit a) (hz : IsUnit z)
    (hdvd : (2 : ℤ_[2]) ^ 3 ∣ a * z ^ 2 - c) :
    ∃ z' : ℤ_[2], a * z' ^ 2 = c ∧ IsUnit z' := by
  let f : Polynomial ℤ_[2] := C a * X ^ 2 - C c
  have ha_norm : ‖(a : ℤ_[2])‖ = 1 := PadicInt.isUnit_iff.mp ha
  have hz_norm : ‖(z : ℤ_[2])‖ = 1 := PadicInt.isUnit_iff.mp hz
  have hf_aeval : Polynomial.aeval z f = a * z ^ 2 - c := by
    simp [f, aeval_def, eval₂_eq_eval_map]
  have hf_deriv_aeval : Polynomial.aeval z f.derivative = 2 * a * z := by
    simp [f, derivative_sub, derivative_mul, derivative_C, derivative_pow, derivative_X,
          aeval_def, eval₂_eq_eval_map]; ring
  have hnorm_f : ‖Polynomial.aeval z f‖ ≤ ‖(2 : ℤ_[2])‖ ^ 3 := by
    rw [hf_aeval]
    obtain ⟨c', hc'⟩ := hdvd
    rw [hc', norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one c')
  have hensel_cond : ‖Polynomial.aeval z f‖ < ‖Polynomial.aeval z f.derivative‖ ^ 2 := by
    rw [hf_deriv_aeval, norm_mul, norm_mul, norm_two_padic, ha_norm, hz_norm]
    calc ‖Polynomial.aeval z f‖ ≤ ‖(2 : ℤ_[2])‖ ^ 3 := hnorm_f
      _ = ((2 : ℝ)⁻¹) ^ 3 := by rw [norm_two_padic]
      _ < ((2 : ℝ)⁻¹ * 1 * 1) ^ 2 := by norm_num
  obtain ⟨z', hz'_root, hz'_close, _, _⟩ := hensels_lemma hensel_cond
  have hz'_unit : IsUnit z' := by
    rw [PadicInt.isUnit_iff]
    have hsub : ‖z' - z‖ < ‖z‖ := by
      calc ‖z' - z‖ < ‖Polynomial.aeval z f.derivative‖ := hz'_close
        _ = ‖2 * a * z‖ := by rw [hf_deriv_aeval]
        _ = ‖(2 : ℤ_[2])‖ * ‖a‖ * ‖z‖ := by rw [norm_mul, norm_mul]
        _ = (2 : ℝ)⁻¹ * 1 * 1 := by rw [norm_two_padic, ha_norm, hz_norm]
        _ < 1 := by norm_num
        _ = ‖z‖ := hz_norm.symm
    have : ‖z'‖ = ‖z‖ := by
      simp only [PadicInt.norm_def] at *
      exact Padic.norm_eq_of_norm_sub_lt_right (by exact_mod_cast hsub)
    rw [this, hz_norm]
  have heq' : a * z' ^ 2 = c := by
    simp [f, aeval_def, eval₂_eq_eval_map] at hz'_root
    exact sub_eq_zero.mp hz'_root
  exact ⟨z', heq', hz'_unit⟩

/-- The underlying $\mathbb{Q}_2$-value of `padicUnit_one u` is the image of `u`. -/
lemma padicUnit_one_val (u : ℤ_[2]ˣ) :
    (padicUnit_one u : ℚ_[2]) = ((↑u : ℤ_[2]) : ℚ_[2]) :=
  IsUnit.unit_spec _

/-- The underlying $\mathbb{Q}_2$-value of `padicUnit_two u` is $2u$. -/
lemma padicUnit_two_val (u : ℤ_[2]ˣ) :
    (padicUnit_two u : ℚ_[2]) = 2 * ((↑u : ℤ_[2]) : ℚ_[2]) :=
  IsUnit.unit_spec _

/-- Equal elements of $\mathbb{Z}_2$ map to equal elements of $\mathbb{Q}_2$. -/
lemma lift_eq_to_Qp {a b : ℤ_[2]} (h : a = b) :
    (a : ℚ_[2]) = (b : ℚ_[2]) :=
  congr_arg Subtype.val h

/-- Lemma 10.8 (case $\alpha = 0$): the equation $z^2 = u x^2 + v y^2$ has a primitive
solution over $\mathbb{Q}_2$ iff it has a primitive solution mod $8$. -/
theorem lemma_10_8_one (u v : ℤ_[2]ˣ) :
    HasPrimitiveSolution (padicUnit_one u) (padicUnit_one v) ↔
    HasPrimitiveSolutionMod8_one u v := by
  constructor
  ·
    intro ⟨x, y, z, hprim, heq⟩
    have heq_Z2 : (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2 = z ^ 2 := by
      rw [padicUnit_one_val, padicUnit_one_val] at heq
      apply Subtype.val_injective
      have h := lift_eq_to_Qp (a := (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2) (b := z ^ 2) ?_
      · exact h
      · apply Subtype.val_injective
        push_cast
        exact heq
    refine ⟨toZModPow 3 x, toZModPow 3 y, toZModPow 3 z, ?_, ?_⟩
    · rcases hprim with hx | hy | hz
      · exact Or.inl (hx.map (toZModPow 3))
      · exact Or.inr (Or.inl (hy.map (toZModPow 3)))
      · exact Or.inr (Or.inr (hz.map (toZModPow 3)))
    · have := congr_arg (toZModPow 3) heq_Z2
      simp only [map_add, map_mul, map_pow] at this; exact this.symm
  ·
    intro ⟨x₀, y₀, z₀, hprim, heq⟩

    obtain ⟨x, hx⟩ := PadicInt.toZModPow_surjective' 3 x₀
    obtain ⟨y, hy⟩ := PadicInt.toZModPow_surjective' 3 y₀
    obtain ⟨z, hz⟩ := PadicInt.toZModPow_surjective' 3 z₀

    have heq_mod : toZModPow 3 (z ^ 2 - ((↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2)) = 0 := by
      simp only [map_sub, map_add, map_mul, map_pow, hx, hy, hz]
      rw [sub_eq_zero]; exact heq
    have hdvd : (2 : ℤ_[2]) ^ 3 ∣ z ^ 2 - ((↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2) :=
      (PadicInt.toZModPow_eq_zero_iff_dvd _ _).mp heq_mod

    rcases hprim with hx_unit | hy_unit | hz_unit
    ·
      have hxu : IsUnit x := by
        have := (hx ▸ hx_unit : IsUnit (toZModPow 3 x))
        rwa [PadicInt.isUnit_toZModPow_iff (by norm_num : (0 : ℕ) < 3)] at this
      have hdvd' : (2 : ℤ_[2]) ^ 3 ∣ (↑u : ℤ_[2]) * x ^ 2 - (z ^ 2 - (↑v : ℤ_[2]) * y ^ 2) := by
        have : (↑u : ℤ_[2]) * x ^ 2 - (z ^ 2 - (↑v : ℤ_[2]) * y ^ 2) =
            -(z ^ 2 - ((↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2)) := by ring
        rw [this]; exact dvd_neg.mpr hdvd
      obtain ⟨x', hx'_eq, hx'_unit⟩ :=
        exists_mul_sq_eq_of_mod8 (Units.isUnit u) hxu hdvd'
      have heq_final : (↑u : ℤ_[2]) * x' ^ 2 + (↑v : ℤ_[2]) * y ^ 2 = z ^ 2 := by
        linear_combination hx'_eq
      refine ⟨x', y, z, Or.inl hx'_unit, ?_⟩
      rw [padicUnit_one_val, padicUnit_one_val]
      have h := congr_arg (Subtype.val : ℤ_[2] → ℚ_[2]) heq_final
      push_cast at h ⊢
      exact h
    ·
      have hyu : IsUnit y := by
        have := (hy ▸ hy_unit : IsUnit (toZModPow 3 y))
        rwa [PadicInt.isUnit_toZModPow_iff (by norm_num : (0 : ℕ) < 3)] at this
      have hdvd' : (2 : ℤ_[2]) ^ 3 ∣ (↑v : ℤ_[2]) * y ^ 2 - (z ^ 2 - (↑u : ℤ_[2]) * x ^ 2) := by
        have : (↑v : ℤ_[2]) * y ^ 2 - (z ^ 2 - (↑u : ℤ_[2]) * x ^ 2) =
            -(z ^ 2 - ((↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2)) := by ring
        rw [this]; exact dvd_neg.mpr hdvd
      obtain ⟨y', hy'_eq, hy'_unit⟩ :=
        exists_mul_sq_eq_of_mod8 (Units.isUnit v) hyu hdvd'
      have heq_final : (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y' ^ 2 = z ^ 2 := by
        linear_combination hy'_eq
      refine ⟨x, y', z, Or.inr (Or.inl hy'_unit), ?_⟩
      rw [padicUnit_one_val, padicUnit_one_val]
      have h := congr_arg (Subtype.val : ℤ_[2] → ℚ_[2]) heq_final
      push_cast at h ⊢
      exact h
    ·
      have hzu : IsUnit z := by
        have := (hz ▸ hz_unit : IsUnit (toZModPow 3 z))
        rwa [PadicInt.isUnit_toZModPow_iff (by norm_num : (0 : ℕ) < 3)] at this
      have hdvd1 : (2 : ℤ_[2]) ^ 3 ∣ 1 * z ^ 2 - ((↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2) := by
        rw [one_mul]; exact hdvd
      obtain ⟨z', hz'_eq, hz'_unit⟩ :=
        exists_mul_sq_eq_of_mod8 isUnit_one hzu hdvd1
      have heq_final : (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2 = z' ^ 2 := by
        rw [one_mul] at hz'_eq; linear_combination -hz'_eq
      refine ⟨x, y, z', Or.inr (Or.inr hz'_unit), ?_⟩
      rw [padicUnit_one_val, padicUnit_one_val]
      have h := congr_arg (Subtype.val : ℤ_[2] → ℚ_[2]) heq_final
      push_cast at h ⊢
      exact h

/-- Brute-force verification: if $x_0$ is a unit and neither $y_0$ nor $z_0$ is a unit, then
$z_0^2 = 2 u_0 x_0^2 + v_0 y_0^2$ has no solution mod $8$. -/
lemma no_prim_sol_two_x_unit :
    ∀ (u₀ v₀ : (ZMod (2 ^ 3))ˣ) (x₀ y₀ z₀ : ZMod (2 ^ 3)),
      IsUnit x₀ → ¬IsUnit y₀ → ¬IsUnit z₀ →
      z₀ ^ 2 = 2 * (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 + (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2 →
      False := by decide

/-- Lemma 10.8 (case $\alpha = 1$): the equation $z^2 = 2u x^2 + v y^2$ has a primitive
solution over $\mathbb{Q}_2$ iff it has a primitive solution mod $8$. -/
theorem lemma_10_8_two (u v : ℤ_[2]ˣ) :
    HasPrimitiveSolution (padicUnit_two u) (padicUnit_one v) ↔
    HasPrimitiveSolutionMod8_two u v := by
  constructor
  ·
    intro ⟨x, y, z, hprim, heq⟩
    have heq_Z2 : 2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2 = z ^ 2 := by
      rw [padicUnit_two_val, padicUnit_one_val] at heq
      suffices h : ((2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2 : ℤ_[2]) : ℚ_[2]) =
                   ((z ^ 2 : ℤ_[2]) : ℚ_[2]) from Subtype.val_injective h
      push_cast; norm_cast
    refine ⟨toZModPow 3 x, toZModPow 3 y, toZModPow 3 z, ?_, ?_⟩
    · rcases hprim with hx | hy | hz
      · exact Or.inl (hx.map (toZModPow 3))
      · exact Or.inr (Or.inl (hy.map (toZModPow 3)))
      · exact Or.inr (Or.inr (hz.map (toZModPow 3)))
    · have := congr_arg (toZModPow 3) heq_Z2
      simp only [map_add, map_mul, map_pow, map_ofNat] at this
      exact this.symm
  ·
    intro ⟨x₀, y₀, z₀, hprim, heq⟩
    obtain ⟨x, hx⟩ := PadicInt.toZModPow_surjective' 3 x₀
    obtain ⟨y, hy⟩ := PadicInt.toZModPow_surjective' 3 y₀
    obtain ⟨z, hz⟩ := PadicInt.toZModPow_surjective' 3 z₀
    have heq_mod : toZModPow 3 (z ^ 2 - (2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2)) = 0 := by
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, hx, hy, hz]
      rw [sub_eq_zero]; linear_combination heq
    have hdvd : (2 : ℤ_[2]) ^ 3 ∣ z ^ 2 - (2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2) :=
      (PadicInt.toZModPow_eq_zero_iff_dvd _ _).mp heq_mod

    have hyz_unit : IsUnit y₀ ∨ IsUnit z₀ := by
      rcases hprim with hx_unit | hy | hz
      · by_contra h
        push Not at h
        obtain ⟨hny, hnz⟩ := h
        have hu₀ : IsUnit (toZModPow 3 (↑u : ℤ_[2])) := (Units.isUnit u).map _
        have hv₀ : IsUnit (toZModPow 3 (↑v : ℤ_[2])) := (Units.isUnit v).map _
        exact no_prim_sol_two_x_unit hu₀.unit hv₀.unit x₀ y₀ z₀ hx_unit hny hnz
          (by simp only [IsUnit.unit_spec]; exact heq)
      · exact Or.inl hy
      · exact Or.inr hz
    rcases hyz_unit with hy_unit | hz_unit
    ·
      have hyu : IsUnit y := by
        have := (hy ▸ hy_unit : IsUnit (toZModPow 3 y))
        rwa [PadicInt.isUnit_toZModPow_iff (by norm_num : (0 : ℕ) < 3)] at this
      have hdvd' : (2 : ℤ_[2]) ^ 3 ∣
          (↑v : ℤ_[2]) * y ^ 2 - (z ^ 2 - 2 * (↑u : ℤ_[2]) * x ^ 2) := by
        have : (↑v : ℤ_[2]) * y ^ 2 - (z ^ 2 - 2 * (↑u : ℤ_[2]) * x ^ 2) =
            -(z ^ 2 - (2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2)) := by ring
        rw [this]; exact dvd_neg.mpr hdvd
      obtain ⟨y', hy'_eq, hy'_unit⟩ :=
        exists_mul_sq_eq_of_mod8 (Units.isUnit v) hyu hdvd'
      have heq_final : 2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y' ^ 2 = z ^ 2 := by
        linear_combination hy'_eq
      refine ⟨x, y', z, Or.inr (Or.inl hy'_unit), ?_⟩
      rw [padicUnit_two_val, padicUnit_one_val]
      have h := congr_arg (Subtype.val : ℤ_[2] → ℚ_[2]) heq_final
      push_cast at h ⊢; norm_cast
    ·
      have hzu : IsUnit z := by
        have := (hz ▸ hz_unit : IsUnit (toZModPow 3 z))
        rwa [PadicInt.isUnit_toZModPow_iff (by norm_num : (0 : ℕ) < 3)] at this
      have hdvd1 : (2 : ℤ_[2]) ^ 3 ∣
          1 * z ^ 2 - (2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2) := by
        rw [one_mul]; exact hdvd
      obtain ⟨z', hz'_eq, hz'_unit⟩ :=
        exists_mul_sq_eq_of_mod8 isUnit_one hzu hdvd1
      have heq_final : 2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2 = z' ^ 2 := by
        rw [one_mul] at hz'_eq; linear_combination -hz'_eq
      refine ⟨x, y, z', Or.inr (Or.inr hz'_unit), ?_⟩
      rw [padicUnit_two_val, padicUnit_one_val]
      have h := congr_arg (Subtype.val : ℤ_[2] → ℚ_[2]) heq_final
      push_cast at h ⊢; norm_cast

end
