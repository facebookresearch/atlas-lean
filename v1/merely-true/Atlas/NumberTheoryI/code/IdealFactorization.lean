/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization

open scoped nonZeroDivisors
open IsDedekindDomain

noncomputable section IdealFactorization

variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  [IsDedekindDomain R]

lemma finsuppProd_primeIdealPow_ne_zero (exps : HeightOneSpectrum R →₀ ℤ) :
    exps.prod (fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e) ≠ 0 := by
  rw [Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun v _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

def countFinsupp (I : (FractionalIdeal R⁰ K)ˣ) :
    HeightOneSpectrum R →₀ ℤ :=
  ⟨(FractionalIdeal.finite_factors (I : FractionalIdeal R⁰ K)).toFinset,
    fun v => FractionalIdeal.count K v (I : FractionalIdeal R⁰ K),
    fun _ => (FractionalIdeal.finite_factors (I : FractionalIdeal R⁰ K)).mem_toFinset⟩

lemma finsuppProd_countFinsupp_eq (I : (FractionalIdeal R⁰ K)ˣ) :
    (countFinsupp K I).prod (fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e) =
      (I : FractionalIdeal R⁰ K) := by
  have hI : (I : FractionalIdeal R⁰ K) ≠ 0 := Units.ne_zero I
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
      Finsupp.prod, countFinsupp]
  simp only [Finsupp.coe_mk]
  symm
  apply finprod_eq_finset_prod_of_mulSupport_subset
  intro v hv
  simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
  rw [Function.mem_mulSupport] at hv
  intro h; exact hv (by rw [h, zpow_zero])

def fractionalIdeal_mulEquiv_finsupp :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun I := Multiplicative.ofAdd (countFinsupp K I)
  invFun exps := Units.mk0
    ((Multiplicative.toAdd exps).prod (fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e))
    (finsuppProd_primeIdealPow_ne_zero K (Multiplicative.toAdd exps))
  left_inv I := by
    apply Units.ext
    simp only [Units.val_mk0, toAdd_ofAdd]
    exact finsuppProd_countFinsupp_eq K I
  right_inv exps := by
    rw [show exps = Multiplicative.ofAdd (Multiplicative.toAdd exps) from (ofAdd_toAdd _).symm]
    ext v
    show FractionalIdeal.count K v _ = _
    rw [Units.val_mk0]
    exact FractionalIdeal.count_finsuppProd K v _
  map_mul' I J := by
    rw [← ofAdd_add]
    congr 1
    ext v
    show FractionalIdeal.count K v
        ((I * J : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) +
      FractionalIdeal.count K v (J : FractionalIdeal R⁰ K)
    rw [Units.val_mul]
    exact FractionalIdeal.count_mul K v (Units.ne_zero I) (Units.ne_zero J)

theorem fractionalIdeal_mulEquiv_finsupp_apply (I : (FractionalIdeal R⁰ K)ˣ)
    (v : HeightOneSpectrum R) :
    (Multiplicative.toAdd (fractionalIdeal_mulEquiv_finsupp K I)) v =
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) := by
  simp only [fractionalIdeal_mulEquiv_finsupp, MulEquiv.coe_mk, Equiv.coe_fn_mk, toAdd_ofAdd]
  rfl

theorem fractionalIdeal_mulEquiv_finsupp_symm_apply (exps : HeightOneSpectrum R →₀ ℤ) :
    ((fractionalIdeal_mulEquiv_finsupp K).symm (Multiplicative.ofAdd exps) :
      FractionalIdeal R⁰ K) =
      exps.prod (fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e) := by
  simp only [fractionalIdeal_mulEquiv_finsupp, MulEquiv.symm_mk, MulEquiv.coe_mk,
    Equiv.coe_fn_symm_mk, toAdd_ofAdd, Units.val_mk0]

@[deprecated (since := "2025-05-04")]
alias Theorem_3_11 := fractionalIdeal_mulEquiv_finsupp
@[deprecated (since := "2025-05-04")]
alias Theorem_3_11_forward_apply := fractionalIdeal_mulEquiv_finsupp_apply
@[deprecated (since := "2025-05-04")]
alias Theorem_3_11_inverse_apply := fractionalIdeal_mulEquiv_finsupp_symm_apply

end IdealFactorization
