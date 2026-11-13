/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.NoetherNormalization

set_option maxHeartbeats 400000

open Cardinal Polynomial MvPolynomial NoetherNormalization Ideal Nat RingHom List Finset

/-- Over an infinite field, every nonzero univariate polynomial has a
non-root (Lec 3, Lem 3 input). -/
theorem Polynomial.exists_eval_ne_zero {k : Type*} [Field k] [Infinite k]
    {p : Polynomial k} (hp : p ≠ 0) :
    ∃ a : k, p.eval a ≠ 0 :=
  p.exists_eval_ne_zero_of_natDegree_lt_card hp <|
    natCast_lt_aleph0.trans_le (infinite_iff.mp ‹_›)

/-- Over an infinite field, every nonzero polynomial has a non-root. -/
theorem Polynomial.exists_not_isRoot {k : Type*} [Field k] [Infinite k]
    {p : Polynomial k} (hp : p ≠ 0) :
    ∃ a : k, ¬ p.IsRoot a :=
  Polynomial.exists_eval_ne_zero hp

/-- Restatement: over an infinite field, some evaluation of a nonzero
polynomial is `False` as a `Prop` for `IsRoot`. -/
theorem Polynomial.eval_ne_zero_of_infinite {k : Type*} [Field k] [Infinite k]
    {p : Polynomial k} (hp : p ≠ 0) :
    ∃ a : k, Polynomial.IsRoot p a = False := by
  obtain ⟨a, ha⟩ := Polynomial.exists_not_isRoot hp
  exact ⟨a, eq_false ha⟩

/-- Iterated evaluation lemma: evaluating in the outer variable at
`C b` and then the inner at `a` agrees with mapping by `eval a` and
evaluating at `b`. -/
lemma Polynomial.eval_eval_eq_eval_map_eval {k : Type*} [CommSemiring k]
    (p : Polynomial (Polynomial k)) (a b : k) :
    (p.eval (Polynomial.C b)).eval a = (p.map (evalRingHom a)).eval b := by
  induction p using Polynomial.induction_on' with
  | add _ _ hp hq => simp [hp, hq]
  | monomial n c =>
    simp [eval_monomial, map_monomial, eval_C, eval_pow, eval_mul]

/-- Bivariate version: over an infinite field every nonzero polynomial
in two variables has a non-zero evaluation. -/
theorem exists_eval_ne_zero_bivariate {k : Type*} [Field k] [Infinite k]
    {p : Polynomial (Polynomial k)} (hp : p ≠ 0) :
    ∃ (a b : k), (p.eval (Polynomial.C b)).eval a ≠ 0 := by

  have ⟨n, hn⟩ : ∃ n, p.coeff n ≠ 0 := by
    by_contra h; push Not at h
    exact hp (Polynomial.ext (fun n => by simp [h n]))

  obtain ⟨a, ha⟩ := Polynomial.exists_eval_ne_zero hn

  have hmap : p.map (evalRingHom a) ≠ 0 := by
    intro h
    have := congr_arg (fun q => q.coeff n) h
    simp [Polynomial.coeff_map] at this
    exact ha this

  obtain ⟨b, hb⟩ := Polynomial.exists_eval_ne_zero hmap
  exact ⟨a, b, by rwa [Polynomial.eval_eval_eq_eval_map_eval]⟩

/-- Lec 3, Lem 3: over an infinite field every nonzero polynomial in
arbitrarily many variables has a non-vanishing evaluation. -/
theorem MvPolynomial.exists_eval_ne_zero {k : Type*} [Field k] [Infinite k]
    {σ : Type*} {f : MvPolynomial σ k} (hf : f ≠ 0) :
    ∃ v : σ → k, MvPolynomial.eval v f ≠ 0 := by
  by_contra h
  push Not at h
  exact hf (MvPolynomial.funext (fun x => by simp [h x]))

section NagataSubstitution

variable {k : Type*} [Field k] {n : ℕ}

noncomputable section

local notation3 "up" => fun (f : MvPolynomial (Fin (n + 1)) k) => 2 + f.totalDegree
local notation3 "r" => fun (f : MvPolynomial (Fin (n + 1)) k) (i : Fin (n + 1)) => (up f) ^ i.1

/-- Composing the Nagata substitution with its negative inverse yields
the identity. -/
lemma t1_comp_neg (f : MvPolynomial (Fin (n + 1)) k) (c : k) :
    (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]; ext i v; cases i using Fin.cases <;> simp

/-- The Nagata change-of-variables `k`-algebra automorphism of
`k[x_0, …, x_n]` used to make leading coefficients units
(Lec 3, Lem 3). -/
abbrev nagataEquiv (f : MvPolynomial (Fin (n + 1)) k) :
    MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
    (t1_comp_neg f 1) (by simpa using t1_comp_neg f (-1))

/-- Helper: bounds on the digit values used in the Nagata substitution. -/
lemma lt_up_of_mem (f : MvPolynomial (Fin (n + 1)) k) (v : Fin (n + 1) →₀ ℕ)
    (vlt : ∀ i, v i < up f) : ∀ l ∈ ofFn (⇑v : Fin (n+1) → ℕ), l < up f := by grind

/-- Helper: distinct exponent vectors produce distinct weighted sums in
the Nagata-substitution base-`up f` representation. -/
lemma sum_r_mul_ne (f : MvPolynomial (Fin (n + 1)) k)
    (v w : Fin (n + 1) →₀ ℕ)
    (vlt : ∀ i, v i < up f) (wlt : ∀ i, w i < up f) (hne : v ≠ w) :
    ∑ x : Fin (n + 1), (r f x) * v x ≠ ∑ x : Fin (n + 1), (r f x) * w x := by
  intro h; refine hne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up_of_mem f v vlt) (lt_up_of_mem f w wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, mul_comm, List.sum_ofFn] using h

/-- Helper: the degree in the first variable of a Nagata-transformed
monomial equals the weighted sum of its exponents. -/
lemma degreeOf_zero_nagata (f : MvPolynomial (Fin (n + 1)) k)
    (v : Fin (n + 1) →₀ ℕ) {a : k} (ha : a ≠ 0) :
    ((nagataEquiv f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r f i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r f i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

/-- Helper: distinct monomials in the support of `f` map under Nagata
substitution to monomials with distinct degrees in the first variable. -/
lemma degreeOf_ne_of_ne (f : MvPolynomial (Fin (n + 1)) k)
    (v w : Fin (n + 1) →₀ ℕ) (hv : v ∈ f.support) (hw : w ∈ f.support) (hne : v ≠ w) :
    (nagataEquiv f <| monomial v <| coeff v f).degreeOf 0 ≠
    (nagataEquiv f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_nagata _ _ (mem_support_iff.mp hv),
    degreeOf_zero_nagata _ _ (mem_support_iff.mp hw)]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) hne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i)) (by lia)

/-- Helper: the leading coefficient after Nagata transform of a single
monomial equals the original coefficient (viewed in the inner ring). -/
lemma leadingCoeff_finSuccEquiv_nagata (f : MvPolynomial (Fin (n + 1)) k)
    (v : Fin (n + 1) →₀ ℕ) :
    (finSuccEquiv k n ((nagataEquiv f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply, eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((T1 f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

/-- Core of Lec 3, Lem 3: after the Nagata change of variables, the
leading coefficient (in `x_0`) of `f` becomes a unit. -/
lemma nagata_leadingcoeff_isUnit (f : MvPolynomial (Fin (n + 1)) k) (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (nagataEquiv f f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (nagataEquiv f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((nagataEquiv f) (h x))).degree <
      (finSuccEquiv k n ((nagataEquiv f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_ne_of_ne f _ _ h1 vin <| ne_of_not_mem_cons h2
  have hcoeff :
      (finSuccEquiv k n ((nagataEquiv f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n ((nagataEquiv f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]; rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((nagataEquiv f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem vin h]
  rw [leadingCoeff_finSuccEquiv_nagata] at hcoeff
  simpa only [hcoeff, algebraMap_eq] using
    (mem_support_iff.mp vin).isUnit.map (MvPolynomial.C (σ := Fin n))

end

end NagataSubstitution

/-- Lec 3, Lem 3 (existence form): given a polynomial `P` of positive
total degree, there is a `k`-algebra automorphism `phi` making the
leading coefficient of `phi P` (as a polynomial in `x_0`) a unit. -/
theorem MvPolynomial.exists_algEquiv_monic
    {k : Type*} [Field k] [Infinite k]
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) k)
    (hP : 0 < P.totalDegree) :
    ∃ (phi : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k),
      IsUnit (MvPolynomial.finSuccEquiv k n (phi P)).leadingCoeff :=
  ⟨nagataEquiv P, nagata_leadingcoeff_isUnit P (by intro h; simp [h] at hP)⟩

