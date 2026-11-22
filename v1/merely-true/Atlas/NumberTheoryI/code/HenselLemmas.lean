/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Atlas.NumberTheoryI.code.HenselDefs

open Polynomial IsLocalRing Ring

section CompleteDVR

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

noncomputable instance completeDVR_henselianLocalRing : HenselianLocalRing A where
  is_henselian := by
    intro f hf a₀ h₁ h₂
    exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk _))

end CompleteDVR

section HenselSimpleRootLifting

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

theorem hensel_simple_root_lift (f : A[X]) (hf : f.Monic)
    (a_bar : ResidueField A)
    (hroot : aeval a_bar f = 0)
    (hsimple : aeval a_bar (derivative f) ≠ 0) :
    ∃ a : A, f.IsRoot a ∧ residue A a = a_bar := by

  have := (HenselianLocalRing.TFAE A).out 0 1
  exact this.mp inferInstance f hf a_bar hroot hsimple

end HenselSimpleRootLifting

section NewtonIteration

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

theorem hensel_newton (f : A[X]) (a₀ : A)
    (h₁ : f.eval a₀ ∈ maximalIdeal A)
    (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∃ a : A, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal A := by
  classical
  set I := maximalIdeal A
  set f' := derivative f

  let c : ℕ → A := fun n =>
    Nat.recOn n a₀ fun _ b => b - f.eval b * Ring.inverse (f'.eval b)
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse (f'.eval (c n)) := by
    intro n; simp only [c]

  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁

  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    haveI := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert h₂.map (Ideal.Quotient.mk I) using 1
    exact SModEq.def.mp ((hc_mod n).eval _)

  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using h₁
    | succ n ih =>
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg, add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two),
        ← Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i; rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      ·
        rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one,
          Finset.sum_singleton, taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one,
          mul_one, mul_neg, mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n),
          mul_one, add_neg_cancel]
        exact Ideal.zero_mem _
      ·
        refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have aux : n + 2 ≤ i * (n + 1) := by
          trans 2 * (n + 1) <;> nlinarith only [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _

  have cauchy : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal A)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add

  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (cauchy _ _)
  refine ⟨a, ?_, ?_⟩
  ·
    show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal A)] by
      exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  ·
    show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

end NewtonIteration

section HenselNewtonConvergence

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

open IsDiscreteValuationRing in
theorem hensel_newton_valuation (f : A[X]) (a₀ : A)
    (hval : addVal A (f.eval a₀) > 2 * addVal A (f.derivative.eval a₀)) :
    ∃ a : A, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal A := by

  have hf'ne : f.derivative.eval a₀ ≠ 0 := by
    intro h; rw [h, addVal_eq_top_iff.mpr rfl] at hval; simp at hval
  set d := f.derivative.eval a₀ with hd_def

  have hdvd : d ^ 2 ∣ f.eval a₀ := by
    rw [sq, ← addVal_le_iff_dvd, addVal_mul]
    exact le_of_lt (by rwa [two_mul] at hval)
  obtain ⟨q₀, hq₀⟩ := hdvd

  have hq₀_mem : q₀ ∈ maximalIdeal A := by
    by_cases hq0 : q₀ = 0
    · rw [hq0]; exact Ideal.zero_mem _
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hqu
    rw [hq₀, sq, addVal_mul, addVal_mul, addVal_eq_zero_iff.mpr hqu, add_zero] at hval
    rw [show (2 : ℕ∞) * addVal A d = addVal A d + addVal A d from two_mul _] at hval
    exact lt_irrefl _ hval


  have h1 : (X - C a₀) ∣ (f - C (f.eval a₀)) := dvd_iff_isRoot.mpr (by simp [IsRoot])
  obtain ⟨q1, hq1⟩ := h1
  have hq1a : q1.eval a₀ = d := by
    have hderiv : derivative (f - C (f.eval a₀)) = derivative ((X - C a₀) * q1) := by rw [hq1]
    rw [derivative_sub, derivative_C, sub_zero, derivative_mul] at hderiv
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero] at hderiv
    have := congr_arg (fun p => p.eval a₀) hderiv
    simp [eval_add, eval_mul, eval_sub, eval_X, eval_C] at this
    exact this.symm
  have h2 : (X - C a₀) ∣ (q1 - C d) := by
    rw [dvd_iff_isRoot]; simp [IsRoot, hq1a]
  obtain ⟨g, hg⟩ := h2
  have htaylor : f = C (f.eval a₀) + C d * (X - C a₀) + g * (X - C a₀) ^ 2 := by
    linear_combination hq1 + (X - C a₀) * hg


  set H := C q₀ + X + g.comp (C a₀ + C d * X) * X ^ 2 with hH_def

  have hH0 : H.eval 0 ∈ maximalIdeal A := by
    simp [hH_def, eval_add, eval_mul, eval_comp, eval_pow, eval_C, eval_X]
    exact hq₀_mem

  have hH'0 : IsUnit (H.derivative.eval 0) := by
    have : H.derivative.eval 0 = 1 := by
      simp [hH_def, derivative_add, derivative_C, derivative_X, derivative_mul,
        derivative_comp, derivative_pow, eval_add, eval_mul, eval_comp, eval_pow, eval_C, eval_X]
    rw [this]; exact isUnit_one

  obtain ⟨b, hHb, hb_mem⟩ := hensel_newton H 0 hH0 hH'0
  rw [sub_zero] at hb_mem

  have hkey : d ^ 2 * H.eval b = f.eval (a₀ + d * b) := by
    have heval : ∀ x, f.eval x = f.eval a₀ + d * (x - a₀) + g.eval x * (x - a₀) ^ 2 := by
      intro x
      have := congr_arg (fun p => p.eval x) htaylor
      simp [eval_add, eval_mul, eval_sub, eval_pow, eval_C, eval_X] at this
      exact this
    specialize heval (a₀ + d * b)
    simp [hH_def, eval_add, eval_mul, eval_comp, eval_pow, eval_C, eval_X] at heval ⊢
    rw [heval, hq₀]
    ring
  have hroot : f.IsRoot (a₀ + d * b) := by
    show f.eval (a₀ + d * b) = 0
    rw [← hkey, hHb, mul_zero]

  refine ⟨a₀ + d * b, hroot, ?_⟩
  simp only [add_sub_cancel_left]
  exact Ideal.mul_mem_left _ d hb_mem

omit [IsAdicComplete (maximalIdeal A) A] in
lemma isUnit_one_add_mul_of_mem_maximalIdeal {c b : A}
    (hb : b ∈ maximalIdeal A) :
    IsUnit (1 + c * b) := by
  by_contra h
  have hmem : 1 + c * b ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]; exact h
  have h1 : (1 : A) ∈ maximalIdeal A := by
    have := (maximalIdeal A).sub_mem hmem (Ideal.mul_mem_left _ c hb)
    rwa [show (1 + c * b) - c * b = 1 from by ring] at this
  exact (IsLocalRing.maximalIdeal.isMaximal (R := A)).ne_top
    ((Ideal.eq_top_iff_one _).mpr h1)

omit [IsAdicComplete (maximalIdeal A) A] in
lemma addVal_add_eq_of_lt {a b : A}
    (h : IsDiscreteValuationRing.addVal A a < IsDiscreteValuationRing.addVal A b) :
    IsDiscreteValuationRing.addVal A (a + b) = IsDiscreteValuationRing.addVal A a := by
  open IsDiscreteValuationRing in
  rw [AddValuation.map_add_of_distinct_val _ (ne_of_lt h), min_eq_left (le_of_lt h)]

omit [IsAdicComplete (maximalIdeal A) A] in
lemma addVal_eval_sub_ge (p : A[X]) (a a₀ : A) :
    IsDiscreteValuationRing.addVal A (a - a₀) ≤
    IsDiscreteValuationRing.addVal A (p.eval a - p.eval a₀) := by
  open IsDiscreteValuationRing in
  have h : (X - C a₀) ∣ (p - C (p.eval a₀)) :=
    dvd_iff_isRoot.mpr (by simp [IsRoot])
  obtain ⟨q, hq⟩ := h
  have heval : p.eval a - p.eval a₀ = (a - a₀) * q.eval a := by
    have := congr_arg (fun r => r.eval a) hq
    simp [eval_sub, eval_mul, eval_X, eval_C] at this; exact this
  rw [heval, addVal_mul]; exact le_add_right (le_refl _)

open IsDiscreteValuationRing in
open IsDiscreteValuationRing in
theorem hensel_newton_derivative_stability (f : A[X]) (a a₀ : A)
    (hva : addVal A (f.derivative.eval a₀) < addVal A (a - a₀)) :
    addVal A (f.derivative.eval a) = addVal A (f.derivative.eval a₀) := by
  rw [show f.derivative.eval a =
    f.derivative.eval a₀ + (f.derivative.eval a - f.derivative.eval a₀) from by ring]
  apply addVal_add_eq_of_lt
  exact lt_of_lt_of_le hva (addVal_eval_sub_ge _ a a₀)

omit [IsAdicComplete (maximalIdeal A) A] in
open IsDiscreteValuationRing in
theorem hensel_newton_root_unique (f : A[X]) (a a' a₀ : A)
    (hfa : f.IsRoot a) (hfa' : f.IsRoot a')
    (hva : addVal A (f.derivative.eval a₀) < addVal A (a - a₀))
    (hva' : addVal A (f.derivative.eval a₀) < addVal A (a' - a₀)) :
    a = a' := by

  have htaylor : (X - C a) ∣ (f - C (f.eval a)) := dvd_iff_isRoot.mpr (by simp [IsRoot])
  obtain ⟨q1, hq1⟩ := htaylor
  have hq1a : q1.eval a = f.derivative.eval a := by
    have hd : derivative (f - C (f.eval a)) = derivative ((X - C a) * q1) := by rw [hq1]
    rw [derivative_sub, derivative_C, sub_zero, derivative_mul] at hd
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero] at hd
    have := congr_arg (fun p => p.eval a) hd
    simp [eval_add, eval_mul, eval_sub, eval_X, eval_C] at this; exact this.symm
  have h2 : (X - C a) ∣ (q1 - C (f.derivative.eval a)) := by
    rw [dvd_iff_isRoot]; simp [IsRoot, hq1a]
  obtain ⟨g_taylor, hg⟩ := h2
  have htaylor_eq :
      f = C (f.eval a) + C (f.derivative.eval a) * (X - C a) +
        g_taylor * (X - C a) ^ 2 := by
    linear_combination hq1 + (X - C a) * hg

  have heval_a' :
      f.eval a' = f.eval a + f.derivative.eval a * (a' - a) +
        g_taylor.eval a' * (a' - a) ^ 2 := by
    have := congr_arg (fun p => p.eval a') htaylor_eq
    simp [eval_add, eval_mul, eval_sub, eval_pow, eval_C, eval_X] at this; exact this

  rw [hfa, hfa'] at heval_a'
  simp only [zero_add] at heval_a'
  have factored : (a' - a) * (f.derivative.eval a + g_taylor.eval a' * (a' - a)) = 0 := by
    linear_combination -heval_a'
  rcases mul_eq_zero.mp factored with h | h
  · exact eq_of_sub_eq_zero h |>.symm
  · exfalso

    have hva_diff : addVal A (f.derivative.eval a₀) < addVal A (a' - a) := by
      have hsub : min (addVal A (a' - a₀)) (addVal A (a - a₀)) ≤
          addVal A (a' - a) := by
        rw [show a' - a = (a' - a₀) + (-(a - a₀)) from by ring]
        calc min (addVal A (a' - a₀)) (addVal A (a - a₀))
            = min (addVal A (a' - a₀)) (addVal A (-(a - a₀))) := by
              rw [AddValuation.map_neg]
          _ ≤ addVal A ((a' - a₀) + -(a - a₀)) := (addVal A).map_add _ _
      exact lt_of_lt_of_le (lt_min hva' hva) hsub

    have hderiv_eq :
        addVal A (f.derivative.eval a) = addVal A (f.derivative.eval a₀) := by
      rw [show f.derivative.eval a =
        f.derivative.eval a₀ + (f.derivative.eval a - f.derivative.eval a₀) from by ring]
      apply addVal_add_eq_of_lt
      exact lt_of_lt_of_le hva (addVal_eval_sub_ge _ a a₀)

    have heq_neg : f.derivative.eval a = -(g_taylor.eval a' * (a' - a)) :=
      eq_neg_of_add_eq_zero_left h

    have hge : addVal A (f.derivative.eval a₀) < addVal A (f.derivative.eval a) := by
      rw [heq_neg, AddValuation.map_neg, addVal_mul]
      calc addVal A (f.derivative.eval a₀)
          < addVal A (a' - a) := hva_diff
        _ ≤ addVal A (g_taylor.eval a') + addVal A (a' - a) := le_add_left (le_refl _)
    rw [hderiv_eq] at hge
    exact lt_irrefl _ hge

omit [IsAdicComplete (maximalIdeal A) A] in
open IsDiscreteValuationRing in
lemma addVal_lt_addVal_mul_of_mem_maximalIdeal {d q : A}
    (hd : d ≠ 0) (hq : q ∈ maximalIdeal A) (_hq0 : q ≠ 0) :
    addVal A d < addVal A d + addVal A q := by
  have hd_ne_top : addVal A d ≠ ⊤ := by rwa [Ne, addVal_eq_top_iff]
  have hq_pos : (0 : ℕ∞) < addVal A q := by
    rw [pos_iff_ne_zero]
    intro h
    have hqu := addVal_eq_zero_iff.mp h
    rw [mem_maximalIdeal, mem_nonunits_iff] at hq
    exact hq hqu
  calc addVal A d = addVal A d + 0 := (add_zero _).symm
    _ < addVal A d + addVal A q := by
        exact WithTop.add_lt_add_left hd_ne_top hq_pos

open IsDiscreteValuationRing in
theorem hensel_newton_valuation_full (f : A[X]) (a₀ : A)
    (hval : addVal A (f.eval a₀) > 2 * addVal A (f.derivative.eval a₀)) :
    ∃ a : A, f.IsRoot a ∧

      a - a₀ ∈ maximalIdeal A ∧
      addVal A (a - a₀) + 2 * addVal A (f.derivative.eval a₀) ≥
        addVal A (f.eval a₀) ∧

      (∀ a' : A, f.IsRoot a' →
        addVal A (f.derivative.eval a₀) < addVal A (a' - a₀) → a' = a) ∧

      addVal A (f.derivative.eval a) = addVal A (f.derivative.eval a₀) := by

  have hf'ne : f.derivative.eval a₀ ≠ 0 := by
    intro h; rw [h, addVal_eq_top_iff.mpr rfl] at hval; simp at hval
  set d := f.derivative.eval a₀ with hd_def
  have hdvd : d ^ 2 ∣ f.eval a₀ := by
    rw [sq, ← addVal_le_iff_dvd, addVal_mul]
    exact le_of_lt (by rwa [two_mul] at hval)
  obtain ⟨q₀, hq₀⟩ := hdvd
  have hq₀_mem : q₀ ∈ maximalIdeal A := by
    by_cases hq0 : q₀ = 0
    · rw [hq0]; exact Ideal.zero_mem _
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hqu
    rw [hq₀, sq, addVal_mul, addVal_mul, addVal_eq_zero_iff.mpr hqu, add_zero] at hval
    rw [show (2 : ℕ∞) * addVal A d = addVal A d + addVal A d from two_mul _] at hval
    exact lt_irrefl _ hval
  have h1 : (X - C a₀) ∣ (f - C (f.eval a₀)) := dvd_iff_isRoot.mpr (by simp [IsRoot])
  obtain ⟨q1, hq1⟩ := h1
  have hq1a : q1.eval a₀ = d := by
    have hderiv : derivative (f - C (f.eval a₀)) = derivative ((X - C a₀) * q1) := by rw [hq1]
    rw [derivative_sub, derivative_C, sub_zero, derivative_mul] at hderiv
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero] at hderiv
    have := congr_arg (fun p => p.eval a₀) hderiv
    simp [eval_add, eval_mul, eval_sub, eval_X, eval_C] at this
    exact this.symm
  have h2 : (X - C a₀) ∣ (q1 - C d) := by rw [dvd_iff_isRoot]; simp [IsRoot, hq1a]
  obtain ⟨g, hg⟩ := h2
  have htaylor : f = C (f.eval a₀) + C d * (X - C a₀) + g * (X - C a₀) ^ 2 := by
    linear_combination hq1 + (X - C a₀) * hg
  set H := C q₀ + X + g.comp (C a₀ + C d * X) * X ^ 2 with hH_def
  have hH0 : H.eval 0 ∈ maximalIdeal A := by
    simp [hH_def, eval_add, eval_mul, eval_comp, eval_pow, eval_C, eval_X]; exact hq₀_mem
  have hH'0 : IsUnit (H.derivative.eval 0) := by
    have : H.derivative.eval 0 = 1 := by
      simp [hH_def, derivative_add, derivative_C, derivative_X, derivative_mul,
        derivative_comp, derivative_pow, eval_add, eval_mul, eval_comp, eval_pow, eval_C, eval_X]
    rw [this]; exact isUnit_one
  obtain ⟨b, hHb, hb_mem⟩ := hensel_newton H 0 hH0 hH'0
  rw [sub_zero] at hb_mem
  have hkey : d ^ 2 * H.eval b = f.eval (a₀ + d * b) := by
    have heval : ∀ x, f.eval x = f.eval a₀ + d * (x - a₀) + g.eval x * (x - a₀) ^ 2 := by
      intro x
      have := congr_arg (fun p => p.eval x) htaylor
      simp [eval_add, eval_mul, eval_sub, eval_pow, eval_C, eval_X] at this; exact this
    specialize heval (a₀ + d * b)
    simp [hH_def, eval_add, eval_mul, eval_comp, eval_pow, eval_C, eval_X] at heval ⊢
    rw [heval, hq₀]; ring
  have hroot : f.IsRoot (a₀ + d * b) := by
    show f.eval (a₀ + d * b) = 0; rw [← hkey, hHb, mul_zero]
  have hmem : (a₀ + d * b) - a₀ ∈ maximalIdeal A := by
    simp only [add_sub_cancel_left]; exact Ideal.mul_mem_left _ d hb_mem

  have hHb_elem : q₀ + b + g.eval (a₀ + d * b) * b ^ 2 = 0 := by
    have := hHb
    simp [hH_def, eval_add, eval_mul, eval_comp, eval_pow, eval_C, eval_X] at this
    exact this
  have hfact : b * (1 + g.eval (a₀ + d * b) * b) = -q₀ := by
    linear_combination hHb_elem
  have hu : IsUnit (1 + g.eval (a₀ + d * b) * b) :=
    isUnit_one_add_mul_of_mem_maximalIdeal hb_mem
  have hvb : addVal A b = addVal A q₀ := by
    have hv : addVal A (b * (1 + g.eval (a₀ + d * b) * b)) = addVal A (-q₀) := by rw [hfact]
    rw [addVal_mul, AddValuation.map_neg] at hv
    rwa [addVal_eq_zero_iff.mpr hu, add_zero] at hv

  have hbound : addVal A ((a₀ + d * b) - a₀) + 2 * addVal A d ≥
      addVal A (f.eval a₀) := by
    simp only [add_sub_cancel_left]
    rw [hq₀]
    have hlhs : addVal A (d * b) = addVal A d + addVal A b := addVal_mul
    have hrhs : addVal A (d ^ 2 * q₀) = addVal A d + addVal A d + addVal A q₀ := by
      rw [sq, addVal_mul, addVal_mul]
    rw [hlhs, hvb, hrhs, two_mul]
    calc addVal A d + addVal A q₀ + (addVal A d + addVal A d)
        = addVal A d + addVal A d + addVal A q₀ + addVal A d := by ring
      _ ≥ addVal A d + addVal A d + addVal A q₀ := le_add_right (le_refl _)


  have hva_gt : addVal A d < addVal A ((a₀ + d * b) - a₀) := by
    simp only [add_sub_cancel_left, addVal_mul]
    by_cases hb0 : b = 0
    · rw [hb0, addVal_eq_top_iff.mpr rfl]
      calc addVal A d < ⊤ := WithTop.lt_top_iff_ne_top.mpr (addVal_eq_top_iff.not.mpr hf'ne)
        _ ≤ addVal A d + ⊤ := le_add_self
    · exact addVal_lt_addVal_mul_of_mem_maximalIdeal hf'ne hb_mem hb0

  set a := a₀ + d * b
  refine ⟨a, hroot, hmem, hbound, ?_, ?_⟩

  · intro a' hroot' hva'
    exact (hensel_newton_root_unique f a a' a₀ hroot hroot' hva_gt hva').symm

  · exact hensel_newton_derivative_stability f a a₀ hva_gt

end HenselNewtonConvergence
