/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Nilpotent.Basic

set_option maxHeartbeats 800000

/-- The `n`-fold composition of right-multiplication by `a` equals right-multiplication
by `a ^ n`, as a `k`-linear endomorphism of `R`. -/
lemma mulRight_pow {k : Type*} [CommSemiring k] {R : Type*} [Ring R] [Algebra k R]
    (a : R) (n : ℕ) :
    (LinearMap.mulRight k a) ^ n = LinearMap.mulRight k (a ^ n) := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    ext x; simp only [pow_succ, LinearMap.mulRight_apply]
    change (LinearMap.mulRight k a ^ n) ((LinearMap.mulRight k a) x) = _
    rw [LinearMap.mulRight_apply, ih, LinearMap.mulRight_apply, mul_assoc,
        (Commute.self_pow a n).eq]

/-- A finite-dimensional `k`-algebra `R` with no nontrivial idempotents is a local ring.
The proof uses Fitting's lemma: for any `a ∈ R`, the operator `mulRight a` decomposes
`R` as kernel and image of a sufficiently high power, producing an idempotent which by
hypothesis is `0` or `1`, hence either `a` is nilpotent (so `1 - a` is a unit) or `a` is
a unit. -/
theorem isLocalRing_of_finiteDimensional_of_no_nontrivial_idempotents
    (k : Type*) [Field k] (R : Type*) [Ring R] [Nontrivial R]
    [Algebra k R] [FiniteDimensional k R]
    (h_idem : ∀ e : R, e * e = e → e = 0 ∨ e = 1) :
    IsLocalRing R := by
  haveI : IsArtinianRing R := isArtinian_of_tower k inferInstance
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  set f := LinearMap.mulRight k a with hf_def

  obtain ⟨n, hn_pos, hn⟩ : ∃ n, 0 < n ∧ IsCompl (f ^ n).ker (f ^ n).range := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp f.eventually_isCompl_ker_pow_range_pow
    exact ⟨N + 1, Nat.succ_pos N, hN (N + 1) (Nat.le_succ N)⟩
  have hfn : f ^ n = LinearMap.mulRight k (a ^ n) := by rw [hf_def, mulRight_pow]

  obtain ⟨u, hu, e, he, hue⟩ := Submodule.mem_sup.mp
    (hn.sup_eq_top ▸ (Submodule.mem_top : (1 : R) ∈ ⊤))
  have hu_eq : u * a ^ n = 0 := by
    have := LinearMap.mem_ker.mp hu; rwa [hfn, LinearMap.mulRight_apply] at this

  have left_ker : ∀ b x, x ∈ (f ^ n).ker → b * x ∈ (f ^ n).ker := fun b x hx => by
    rw [LinearMap.mem_ker, hfn, LinearMap.mulRight_apply] at hx ⊢
    rw [mul_assoc, hx, mul_zero]
  have left_range : ∀ b x, x ∈ (f ^ n).range → b * x ∈ (f ^ n).range := fun b x hx => by
    rw [hfn] at hx ⊢
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx; rw [LinearMap.mem_range]
    exact ⟨b * y, by simp only [LinearMap.mulRight_apply] at hy ⊢; rw [mul_assoc, hy]⟩
  have disj : ∀ x, x ∈ (f ^ n).ker → x ∈ (f ^ n).range → x = 0 := fun x hK hN => by
    have hmem := Submodule.mem_inf.mpr ⟨hK, hN⟩; rwa [hn.inf_eq_bot] at hmem

  have hee : e * e = e := by
    have sum_eq : e * u + e * e = e := by
      have h1 : e * (u + e) = e := by rw [hue, mul_one]
      rwa [mul_add] at h1
    have heu0 : e * u = 0 := disj _ (left_ker e u hu) (by
      rw [show e * u = e - e * e from eq_sub_iff_add_eq.mpr sum_eq]
      exact ((f ^ n).range).sub_mem he (left_range e e he))
    rw [heu0, zero_add] at sum_eq; exact sum_eq

  rcases h_idem e hee with he0 | he1
  ·
    right
    have hu1 : u = 1 := by rwa [he0, add_zero] at hue
    exact IsNilpotent.isUnit_one_sub ⟨n, by rw [← one_mul (a ^ n), ← hu1, hu_eq]⟩
  ·
    left
    rw [hfn] at he; rw [he1] at he
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp he
    simp only [LinearMap.mulRight_apply] at hw
    have haunit : IsUnit (a ^ n) := IsUnit.of_mul_eq_one_right w hw
    rw [← Nat.succ_pred_eq_of_pos hn_pos, pow_succ] at haunit
    exact isUnit_of_mul_isUnit_right haunit
