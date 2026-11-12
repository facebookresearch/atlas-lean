/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Algebra.MvPolynomial.Degrees

noncomputable section
open PadicInt Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

/-- The diagonal quadratic multivariate polynomial $\sum_i a_i X_i^2$ over $\mathbb{Z}/p$. -/
def diagQuadMvPoly {n : ℕ} (a : Fin n → ZMod p) :
    MvPolynomial (Fin n) (ZMod p) :=
  ∑ i : Fin n, MvPolynomial.C (a i) * (MvPolynomial.X i) ^ 2

/-- **Chevalley-Warning consequence.** For $n > 2$, any diagonal quadratic form
$\sum_i a_i y_i^2$ over $\mathbb{Z}/p$ has a nontrivial zero. -/
lemma exists_nontrivial_zero_mod_p {n : ℕ} (hn : 2 < n) (a : Fin n → ZMod p) :
    ∃ y : Fin n → ZMod p, (∃ i, y i ≠ 0) ∧ ∑ i, a i * (y i) ^ 2 = 0 := by
  classical
  set S := {x : Fin n → ZMod p // MvPolynomial.eval x (diagQuadMvPoly a) = 0}
  have hdeg : (diagQuadMvPoly a).totalDegree < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    calc (diagQuadMvPoly a).totalDegree ≤ 2 := by
          apply MvPolynomial.totalDegree_finsetSum_le; intro i _
          calc (MvPolynomial.C (a i) * MvPolynomial.X i ^ 2).totalDegree
              ≤ (MvPolynomial.C (a i)).totalDegree + (MvPolynomial.X i ^ 2).totalDegree :=
                MvPolynomial.totalDegree_mul _ _
            _ ≤ 0 + 2 := by
                gcongr
                · exact le_of_eq (MvPolynomial.totalDegree_C _)
                · simp
            _ = 2 := by omega
      _ < n := hn
  have hchar : p ∣ Fintype.card S := char_dvd_card_solutions p hdeg
  have hzero : MvPolynomial.eval 0 (diagQuadMvPoly a) = 0 := by
    simp [diagQuadMvPoly, map_sum]
  have hcard_pos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨⟨0, hzero⟩⟩
  have hcard_ge : 2 ≤ Fintype.card S :=
    le_trans hp.out.two_le (Nat.le_of_dvd hcard_pos hchar)
  have hexists : ∃ x : S, x.val ≠ 0 := by
    by_contra hall; push Not at hall
    have : Fintype.card S ≤ 1 := by
      rw [Fintype.card_le_one_iff]; intro ⟨a', ha'⟩ ⟨b', hb'⟩
      ext1; rw [hall ⟨a', ha'⟩, hall ⟨b', hb'⟩]
    omega
  obtain ⟨⟨y, hy⟩, hyne⟩ := hexists
  refine ⟨y, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hyne; exact ⟨i, by simpa using hi⟩
  · simp only [diagQuadMvPoly, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
          MvPolynomial.eval_X, MvPolynomial.eval_C] at hy; exact hy

/-- If a natural number $n$ is not divisible by $p$, then the $p$-adic norm of $n$ is $1$. -/
lemma norm_natCast_eq_one_of_not_dvd (n : ℕ) (hn : ¬ (p ∣ n)) :
    ‖(n : ℤ_[p])‖ = 1 := by
  apply le_antisymm (norm_le_one _)
  rw [not_lt.symm]
  intro hlt
  have hdvd : (p : ℤ_[p]) ∣ (n : ℤ_[p]) := (norm_lt_one_iff_dvd _).mp hlt
  have hmem : (n : ℤ_[p]) ∈ RingHom.ker toZMod := by
    rw [ker_toZMod, maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    exact hdvd
  rw [RingHom.mem_ker, map_natCast] at hmem
  exact hn ((ZMod.natCast_eq_zero_iff n p).mp hmem)

/-- Multiplicativity of the $p$-adic norm on $\mathbb{Z}_p$. -/
lemma norm_mul_padic (a b : ℤ_[p]) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  simp only [norm_def, PadicInt.coe_mul]
  exact Padic.padicNormE.mul _ _

/-- Any unit $u \in \mathbb{Z}_p^\times$ has norm $1$. -/
lemma norm_unit_eq_one (u : ℤ_[p]ˣ) : ‖(u : ℤ_[p])‖ = 1 := by
  rw [← PadicInt.isUnit_iff]; exact u.isUnit

/-- The univariate quadratic polynomial $c + a X^2 \in \mathbb{Z}_p[X]$. -/
def quadPoly (a c : ℤ_[p]) : Polynomial ℤ_[p] :=
  Polynomial.C c + Polynomial.C a * Polynomial.X ^ 2

/-- Evaluation of `quadPoly a c` at $t$ equals $c + a t^2$. -/
lemma quadPoly_aeval (a c t : ℤ_[p]) :
    Polynomial.aeval t (quadPoly a c) = c + a * t ^ 2 := by
  simp [quadPoly, map_add, map_mul, map_pow, aeval_X, aeval_C]

/-- The derivative of `quadPoly a c` equals $2 a X$. -/
lemma quadPoly_derivative_eq (a c : ℤ_[p]) :
    (quadPoly a c).derivative = Polynomial.C (2 * a) * Polynomial.X := by
  simp [quadPoly, derivative_add, derivative_mul, derivative_C, derivative_pow, derivative_X]
  ring

/-- Evaluation of the derivative of `quadPoly a c` at $t$ equals $2 a t$. -/
lemma quadPoly_aeval_derivative (a c t : ℤ_[p]) :
    Polynomial.aeval t (quadPoly a c).derivative = 2 * a * t := by
  rw [quadPoly_derivative_eq]
  simp [map_mul, aeval_C, aeval_X]

/-- **Theorem 11.1.** Over $\mathbb{Q}_p$ with $p$ odd, any diagonal quadratic form
$\sum_{i=1}^n a_i x_i^2$ in more than $2$ variables with unit coefficients
$a_i \in \mathbb{Z}_p^\times$ has a nontrivial zero. The proof combines Chevalley-Warning
(for a nontrivial zero mod $p$) with Hensel's lemma (to lift to $\mathbb{Z}_p$). -/
theorem diagonal_unit_form_represents_zero
    (hodd : p ≠ 2)
    {n : ℕ} (hn : 2 < n)
    (a : Fin n → ℤ_[p]ˣ) :
    ∃ x : Fin n → ℚ_[p], (∃ i, x i ≠ 0) ∧
      ∑ i, (a i : ℚ_[p]) * x i ^ 2 = 0 := by

  set ā : Fin n → ZMod p := fun i => toZMod (a i : ℤ_[p]) with hā_def

  obtain ⟨y, ⟨j, hyj⟩, hsum⟩ := exists_nontrivial_zero_mod_p hn ā

  set ŷ : Fin n → ℤ_[p] := fun i => ((ZMod.val (y i) : ℕ) : ℤ_[p]) with hŷ_def

  have hsum_ker : ∑ i, (a i : ℤ_[p]) * ŷ i ^ 2 ∈ RingHom.ker toZMod := by
    rw [RingHom.mem_ker, map_sum]
    simp_rw [map_mul, map_pow, show ∀ i, toZMod (ŷ i) = y i from
      fun i => by simp [hŷ_def]]
    exact hsum
  have hsum_lt : ‖∑ i, (a i : ℤ_[p]) * ŷ i ^ 2‖ < 1 := by
    rw [ker_toZMod, maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hsum_ker
    exact (norm_lt_one_iff_dvd _).mpr hsum_ker

  have hyj_norm : ‖ŷ j‖ = 1 := by
    apply norm_natCast_eq_one_of_not_dvd
    intro hdvd
    exact hyj (by rw [← ZMod.val_eq_zero]; exact Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _))


  set c := ∑ i, (a i : ℤ_[p]) * ŷ i ^ 2 - (a j : ℤ_[p]) * ŷ j ^ 2 with hc_def

  have hg_eval : Polynomial.aeval (ŷ j) (quadPoly (a j : ℤ_[p]) c) =
      ∑ i, (a i : ℤ_[p]) * ŷ i ^ 2 := by
    rw [quadPoly_aeval, hc_def]; ring

  have hderiv_eval : Polynomial.aeval (ŷ j) (quadPoly (a j : ℤ_[p]) c).derivative =
      2 * (a j : ℤ_[p]) * ŷ j := by
    exact quadPoly_aeval_derivative _ _ _

  have hderiv_norm : ‖Polynomial.aeval (ŷ j) (quadPoly (a j : ℤ_[p]) c).derivative‖ = 1 := by
    rw [hderiv_eval, norm_mul_padic, norm_mul_padic]
    have h2 : ‖(2 : ℤ_[p])‖ = 1 := by
      apply norm_natCast_eq_one_of_not_dvd
      intro h
      have : p ≤ 2 := Nat.le_of_dvd (by omega) h
      have : 2 ≤ p := hp.out.two_le
      omega
    rw [h2, norm_unit_eq_one, hyj_norm, mul_one, mul_one]

  have hhensel_cond : ‖Polynomial.aeval (ŷ j) (quadPoly (a j : ℤ_[p]) c)‖ <
      ‖Polynomial.aeval (ŷ j) (quadPoly (a j : ℤ_[p]) c).derivative‖ ^ 2 := by
    rw [hg_eval, hderiv_norm]; simp; exact hsum_lt

  obtain ⟨z, hz_root, _, _, _⟩ := hensels_lemma hhensel_cond

  have hz_eq : c + (a j : ℤ_[p]) * z ^ 2 = 0 := by
    have := hz_root; rwa [quadPoly_aeval] at this

  set x : Fin n → ℚ_[p] := fun i => if i = j then (z : ℚ_[p]) else (ŷ i : ℚ_[p])
  refine ⟨x, ?_, ?_⟩
  ·
    refine ⟨j, ?_⟩
    simp only [x, ite_true]
    apply PadicInt.coe_ne_zero.mpr
    intro hz; subst hz
    have hc_zero : c = 0 := by
      rwa [quadPoly_aeval, zero_pow (two_ne_zero), mul_zero, add_zero] at hz_root
    have hsum_eq : ∑ i, (a i : ℤ_[p]) * ŷ i ^ 2 = (a j : ℤ_[p]) * ŷ j ^ 2 := by
      have h := hc_def
      rw [hc_zero] at h

      exact sub_eq_zero.mp h.symm
    have : ‖(a j : ℤ_[p]) * ŷ j ^ 2‖ = 1 := by
      rw [norm_mul_padic, norm_unit_eq_one, sq, norm_mul_padic, hyj_norm, mul_one, one_mul]
    linarith [hsum_eq ▸ hsum_lt]
  ·


    have hzp : (a j : ℤ_[p]) * z ^ 2 +
        ∑ i ∈ Finset.univ.erase j, (a i : ℤ_[p]) * ŷ i ^ 2 = 0 := by
      have hc' : ∑ i ∈ Finset.univ.erase j, (a i : ℤ_[p]) * ŷ i ^ 2 = c := by
        rw [hc_def, ← Finset.add_sum_erase Finset.univ
          (fun i => (a i : ℤ_[p]) * ŷ i ^ 2) (Finset.mem_univ j)]
        ring
      rw [hc', add_comm]; exact hz_eq

    have := congr_arg (fun x : ℤ_[p] => (x : ℚ_[p])) hzp
    simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_sum,
      PadicInt.coe_zero] at this

    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [x, ite_true]
    convert this using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [(Finset.mem_erase.mp hi).1]
