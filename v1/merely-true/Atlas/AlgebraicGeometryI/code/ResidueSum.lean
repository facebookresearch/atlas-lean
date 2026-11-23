/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

open Polynomial Finset BigOperators

variable {k : Type*} [Field k]

namespace ResidueSum

/-- The residue of `P/Q` at a simple pole `a`: `P(a) / Q'(a)`, the standard
formula valid when `Q` has a simple root at `a`. -/
noncomputable def residueAtPole (P Q : k[X]) (a : k) : k :=
  P.eval a / Q.derivative.eval a

/-- The product `∏ (X − a_i)` whose roots are the chosen poles, the denominator
of the partial fraction decomposition. -/
noncomputable def poleProd {n : ℕ} (a : Fin n → k) : k[X] :=
  ∏ i : Fin n, (X - C (a i))

/-- The numerator polynomial `Σ_i c_i · ∏_{j ≠ i}(X − a_j)` of a partial-fraction
expression with residues `c_i` at the poles `a_i`. -/
noncomputable def partialFracNumer {n : ℕ} (c a : Fin n → k) : k[X] :=
  ∑ i : Fin n, C (c i) * ∏ j ∈ Finset.univ.erase i, (X - C (a j))

/-- The residue at the pole `a_i` of the partial-fraction differential
`partialFracNumer c a / poleProd a`. -/
noncomputable def residuePartialFrac {n : ℕ} (c : Fin n → k) (a : Fin n → k)
    (i : Fin n) : k :=
  residueAtPole (partialFracNumer c a) (poleProd a) (a i)

/-- The residue at infinity of the partial-fraction differential: the negative
of the leading coefficient of the numerator polynomial. -/
noncomputable def residueAtInfPartialFrac {n : ℕ} (c : Fin n → k) (a : Fin n → k) : k :=
  -((partialFracNumer c a).coeff (n - 1))

/-- For distinct indices, the product `∏_{l ≠ i}(X − a_l)` evaluated at `a_j`
vanishes (one factor `a_j − a_j` appears). -/
lemma prod_erase_eval_zero {n : ℕ} (a : Fin n → k) (i j : Fin n) (hij : i ≠ j) :
    (∏ l ∈ Finset.univ.erase i, (X - C (a l))).eval (a j) = 0 := by
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩) (by simp)

/-- The leading coefficient of the `i`-th summand `c_i · ∏_{j ≠ i}(X − a_j)` is
exactly `c_i`. -/
lemma coeff_summand {n : ℕ} (c a : Fin n → k) (i : Fin n) :
    (C (c i) * ∏ j ∈ Finset.univ.erase i, (X - C (a j))).coeff (n - 1) = c i := by
  rw [Polynomial.coeff_C_mul]
  have hm : (∏ j ∈ Finset.univ.erase i, (X - C (a j))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C (a j))
  have hd : (∏ j ∈ Finset.univ.erase i, (X - C (a j))).natDegree = n - 1 := by
    rw [Polynomial.natDegree_prod _ _ (fun j _ => (monic_X_sub_C (a j)).ne_zero)]
    simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  have : (∏ j ∈ Finset.univ.erase i, (X - C (a j))).coeff (n - 1) = 1 := by
    conv_lhs => rw [← hd]
    exact hm.leadingCoeff
  rw [this, mul_one]

/-- Single-pole identity: the residue of `c / (X − a)` at `a` equals `c`. -/
theorem residue_of_simple_pole (c a : k) :
    residueAtPole (C c) (X - C a) a = c := by
  simp [residueAtPole, derivative_sub, derivative_X, derivative_C]

/-- Evaluation of the partial-fraction numerator at a pole `a_j`: only the
`j`-th summand survives and equals `c_j · ∏_{l ≠ j}(a_j − a_l)`. -/
theorem partialFracNumer_eval {n : ℕ} (c a : Fin n → k) (j : Fin n) :
    (partialFracNumer c a).eval (a j) =
    c j * ∏ l ∈ Finset.univ.erase j, (a j - a l) := by
  unfold partialFracNumer
  simp only [eval_finset_sum, eval_mul, eval_C]
  rw [Finset.sum_eq_single j]
  · simp [eval_prod, eval_sub, eval_X, eval_C]
  · intro i _ hij
    simp only [eval_prod, eval_sub, eval_X, eval_C]
    have : (∏ l ∈ Finset.univ.erase i, (a j - a l)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩) (by simp)
    rw [this]; ring
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- Logarithmic derivative formula: at a pole `a_j` of the denominator
`∏(X − a_i)`, the derivative evaluates to `∏_{i ≠ j}(a_j − a_i)`. -/
theorem poleProd_derivative_eval {n : ℕ} (a : Fin n → k) (j : Fin n) :
    (poleProd a).derivative.eval (a j) = ∏ i ∈ Finset.univ.erase j, (a j - a i) := by
  unfold poleProd
  rw [Polynomial.derivative_prod_finset]
  simp only [eval_finset_sum, derivative_sub, derivative_X, derivative_C, sub_zero, mul_one]
  rw [Finset.sum_eq_single j]
  · simp [eval_prod, eval_sub, eval_X, eval_C]
  · intro i _ hij
    have := prod_erase_eval_zero a i j hij
    simp [this]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- The leading (degree `n−1`) coefficient of the partial-fraction numerator
equals the sum of the residues `Σ c_i`. -/
theorem partialFracNumer_coeff_top {n : ℕ} (c a : Fin n → k) :
    (partialFracNumer c a).coeff (n - 1) = ∑ i, c i := by
  unfold partialFracNumer
  simp only [Polynomial.finset_sum_coeff]
  exact Finset.sum_congr rfl (fun i _ => coeff_summand c a i)

/-- Derivative of `(X − a) · R` at `a` is simply `R(a)` (the product rule
specialised to a simple linear factor). -/
theorem derivative_at_simple_root (a : k) (R : k[X]) :
    ((X - C a) * R).derivative.eval a = R.eval a := by
  simp [derivative_mul, derivative_sub, derivative_X, derivative_C]

/-- Residue formula in factored form: the residue of `P / ((X − a) · R)` at `a`
equals `P(a) / R(a)` when `R(a) ≠ 0`. -/
theorem residue_eq_eval_div_cofactor (P R : k[X]) (a : k) (_hR : R.eval a ≠ 0) :
    residueAtPole P ((X - C a) * R) a = P.eval a / R.eval a := by
  unfold residueAtPole; rw [derivative_at_simple_root]

/-- The residue at the pole `a_j` of the canonical partial-fraction differential
returns the input coefficient `c_j`. -/
theorem residue_partial_frac_eq_coeff {n : ℕ} (c a : Fin n → k) (j : Fin n)
    (hdist : Function.Injective a) :
    residuePartialFrac c a j = c j := by
  unfold residuePartialFrac residueAtPole
  rw [partialFracNumer_eval, poleProd_derivative_eval]
  have hprod : ∏ l ∈ Finset.univ.erase j, (a j - a l) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi; rw [Finset.mem_erase] at hi
    exact sub_ne_zero.mpr (fun h => hi.1 (hdist h.symm))
  field_simp

/-- The residue at infinity of the partial-fraction differential equals
`−Σ c_i`, the negative of the sum of finite residues. -/
theorem residueAtInf_eq_neg_sum {n : ℕ} (c a : Fin n → k) :
    residueAtInfPartialFrac c a = -(∑ i, c i) := by
  unfold residueAtInfPartialFrac; rw [partialFracNumer_coeff_top]

/-- Residue theorem for `ℙ¹` in partial-fraction form: the sum of all residues
(finite poles plus infinity) of a rational differential is zero. -/
theorem residue_sum_partial_frac {n : ℕ} (c : Fin n → k) (a : Fin n → k)
    (hdist : Function.Injective a) :
    (∑ i, residuePartialFrac c a i) + residueAtInfPartialFrac c a = 0 := by
  have h1 : ∀ i, residuePartialFrac c a i = c i :=
    fun i => residue_partial_frac_eq_coeff c a i hdist
  simp_rw [h1, residueAtInf_eq_neg_sum, add_neg_cancel]

/-- Worked example with two simple poles: residues of `c / ((X − a)(X − b))`
at `a` and `b` cancel to zero (no pole at infinity). -/
theorem residue_sum_const_over_two_linear (a b c : k) (hab : a ≠ b) :
    residueAtPole (C c) ((X - C a) * (X - C b)) a +
    residueAtPole (C c) ((X - C a) * (X - C b)) b = 0 := by
  simp only [residueAtPole, eval_C]
  simp [derivative_mul, derivative_sub, derivative_X, derivative_C]
  have h1 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h2 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  field_simp; ring

/-- Residue identity with a degree-one numerator: `Σ res P/((X−a)(X−b)) + (−[X]P) = 0`,
where the last term is the residue at infinity. -/
theorem residue_sum_poly_two_poles {P : k[X]} (a b : k)
    (hab : a ≠ b) (hP : P.natDegree ≤ 1) :
    residueAtPole P ((X - C a) * (X - C b)) a +
    residueAtPole P ((X - C a) * (X - C b)) b +
    (-P.coeff 1) = 0 := by
  simp only [residueAtPole]
  simp [derivative_mul, derivative_sub, derivative_X, derivative_C]
  have h1 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h2 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hP_eq : P = C (P.coeff 0) + C (P.coeff 1) * X := by
    ext n; simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X]
    match n with
    | 0 => simp
    | 1 => simp
    | n + 2 =>
      have : P.coeff (n + 2) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this]
  rw [hP_eq]; simp [eval_add, eval_mul, eval_C, eval_X]; field_simp; ring

/-- Pure-algebra check for the two-pole identity: a fraction identity that
underpins the residue cancellation in `residue_sum_poly_two_poles`. -/
theorem residue_sum_linear_over_two_poles (a b d e : k) (hab : a ≠ b) :
    (d * a + e) / (a - b) + (d * b + e) / (b - a) + (-d) = 0 := by
  have h1 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h2 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  field_simp; ring

/-- Combinatorial form of the residue theorem for a logarithmic differential
`d log(f)`: zeros contribute `+1`, poles contribute `−1`, and infinity
contributes `(deg poles) − (deg zeros)`. The total is zero. -/
theorem residue_sum_logarithmic_form {n m : ℕ}
    (_zeros : Fin n → k) (_poles : Fin m → k) :
    (∑ _i : Fin n, (1 : k)) + (∑ _j : Fin m, (-1 : k)) +
    ((↑m : k) - (↑n : k)) = 0 := by
  simp [Finset.sum_const]; ring

end ResidueSum
