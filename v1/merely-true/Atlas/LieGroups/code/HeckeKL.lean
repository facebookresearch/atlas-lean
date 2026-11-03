/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Atlas.LieGroups.code.CompositionSeries

noncomputable section

open Polynomial

abbrev HeckeCoeffRing := LaurentPolynomial ℤ

def heckeQ : HeckeCoeffRing := LaurentPolynomial.T 2

abbrev hecke_q : HeckeCoeffRing := heckeQ

structure CoxeterGroupData where
  W : Type*
  grpInst : Group W
  finInst : Fintype W
  decEq : DecidableEq W
  simpleReflections : Finset W
  length : W → ℕ
  length_one : length 1 = 0
  length_simple : ∀ s ∈ simpleReflections, length s = 1
  simple_sq : ∀ s ∈ simpleReflections, s * s = 1
  bruhatLE : W → W → Prop
  bruhatLE_dec : ∀ y w, Decidable (bruhatLE y w)
  bruhat_refl : ∀ w, bruhatLE w w
  bruhat_trans : ∀ x y z, bruhatLE x y → bruhatLE y z → bruhatLE x z
  bruhat_antisymm : ∀ x y, bruhatLE x y → bruhatLE y x → x = y
  bruhat_length_le : ∀ y w, bruhatLE y w → length y ≤ length w
  bruhat_length_strict : ∀ y w, bruhatLE y w → y ≠ w → length y < length w
  exchange_left : ∀ s ∈ simpleReflections, ∀ w,
    length (s * w) = length w + 1 ∨ length (s * w) + 1 = length w
  descentRefl : W → W
  descentRefl_simple : ∀ y, y ≠ 1 → descentRefl y ∈ simpleReflections
  descentRefl_length : ∀ y, y ≠ 1 → length (descentRefl y * y) < length y
  descentRefl_of_mul : ∀ s ∈ simpleReflections, ∀ w,
    length (s * w) = length w + 1 → descentRefl (s * w) = s

attribute [instance] CoxeterGroupData.grpInst CoxeterGroupData.finInst
  CoxeterGroupData.decEq

instance (C : CoxeterGroupData) (y w : C.W) : Decidable (C.bruhatLE y w) :=
  C.bruhatLE_dec y w

abbrev HeckeAlgebra (C : CoxeterGroupData) := C.W →₀ HeckeCoeffRing

instance HeckeAlgebra.instAddCommMonoid (C : CoxeterGroupData) :
    AddCommMonoid (HeckeAlgebra C) := Finsupp.instAddCommMonoid

instance HeckeAlgebra.instAddCommGroup (C : CoxeterGroupData) :
    AddCommGroup (HeckeAlgebra C) := Finsupp.instAddCommGroup

instance HeckeAlgebra.instModule (C : CoxeterGroupData) :
    Module HeckeCoeffRing (HeckeAlgebra C) := Finsupp.module C.W HeckeCoeffRing

def HeckeAlgebra.T (C : CoxeterGroupData) (w : C.W) : HeckeAlgebra C :=
  Finsupp.single w 1

def simpleReflMulBasis (C : CoxeterGroupData) (s w : C.W) : HeckeAlgebra C :=
  if C.length (s * w) = C.length w + 1 then
    Finsupp.single (s * w) 1
  else
    Finsupp.single w (hecke_q - 1) + Finsupp.single (s * w) hecke_q

def simpleActOnLinComb (C : CoxeterGroupData) (s : C.W) (f : HeckeAlgebra C) : HeckeAlgebra C :=
  f.sum fun w c => c • simpleReflMulBasis C s w

def heckeMulBasis (C : CoxeterGroupData) (w₁ w₂ : C.W) : HeckeAlgebra C :=
  if hw₁ : w₁ = 1 then Finsupp.single w₂ 1
  else
    let s := C.descentRefl w₁
    let w₁' := s * w₁
    simpleActOnLinComb C s (heckeMulBasis C w₁' w₂)
termination_by C.length w₁
decreasing_by exact C.descentRefl_length w₁ hw₁

def heckeMul (C : CoxeterGroupData) (f g : HeckeAlgebra C) : HeckeAlgebra C :=
  f.sum fun w₁ a₁ => g.sum fun w₂ a₂ =>
    (a₁ * a₂) • heckeMulBasis C w₁ w₂

lemma CoxeterGroupData.simple_cancel (C : CoxeterGroupData) (s : C.W)
    (hs : s ∈ C.simpleReflections) (w : C.W) : s * (s * w) = w := by
  rw [← mul_assoc, C.simple_sq s hs, one_mul]

lemma CoxeterGroupData.length_zero_eq_one (C : CoxeterGroupData) (w : C.W)
    (h : C.length w = 0) : w = 1 := by
  by_contra hw; have := C.descentRefl_length w hw; omega

lemma CoxeterGroupData.simple_ne_one (C : CoxeterGroupData) (s : C.W)
    (hs : s ∈ C.simpleReflections) : s ≠ 1 := by
  intro h; subst h; have := C.length_simple 1 hs; rw [C.length_one] at this; omega

lemma CoxeterGroupData.descentRefl_of_simple (C : CoxeterGroupData) (s : C.W)
    (hs : s ∈ C.simpleReflections) : C.descentRefl s = s := by
  have hs_ne : s ≠ 1 := C.simple_ne_one s hs
  have h1 : C.length (C.descentRefl s * s) = 0 := by
    have := C.descentRefl_length s hs_ne
    have := C.length_simple s hs
    omega
  have h2 : C.descentRefl s * s = 1 := C.length_zero_eq_one _ h1
  calc C.descentRefl s = C.descentRefl s * 1 := (mul_one _).symm
    _ = C.descentRefl s * (s * s) := by rw [C.simple_sq s hs]
    _ = (C.descentRefl s * s) * s := (mul_assoc _ _ _).symm
    _ = 1 * s := by rw [h2]
    _ = s := one_mul s

lemma simpleActOnLinComb_single (C : CoxeterGroupData) (s w : C.W) (c : HeckeCoeffRing) :
    simpleActOnLinComb C s (Finsupp.single w c) = c • simpleReflMulBasis C s w := by
  unfold simpleActOnLinComb
  rw [Finsupp.sum_single_index]
  simp [zero_smul]

lemma heckeMulBasis_one_left (C : CoxeterGroupData) (w : C.W) :
    heckeMulBasis C 1 w = Finsupp.single w 1 := by
  simp [heckeMulBasis]

lemma heckeMulBasis_one_right (C : CoxeterGroupData) (w₁ : C.W) :
    heckeMulBasis C w₁ 1 = Finsupp.single w₁ 1 := by
  induction hn : C.length w₁ using Nat.strongRecOn generalizing w₁ with
  | ind n ih =>
  by_cases hw₁ : w₁ = 1
  · subst hw₁; simp [heckeMulBasis]
  · rw [heckeMulBasis]; simp only [hw₁, ↓reduceDIte]
    set s := C.descentRefl w₁
    set w₁' := s * w₁
    have hs : s ∈ C.simpleReflections := C.descentRefl_simple w₁ hw₁
    have hlen : C.length w₁' < C.length w₁ := C.descentRefl_length w₁ hw₁
    have sw₁'_eq : s * w₁' = w₁ := C.simple_cancel s hs w₁
    have ih_w₁' : heckeMulBasis C w₁' 1 = Finsupp.single w₁' 1 :=
      ih (C.length w₁') (by omega) w₁' rfl
    rw [ih_w₁', simpleActOnLinComb_single, one_smul]
    unfold simpleReflMulBasis
    have : C.length (s * w₁') = C.length w₁' + 1 := by
      rcases C.exchange_left s hs w₁' with h | h
      · exact h
      · exfalso; rw [sw₁'_eq] at h; omega
    rw [if_pos this, sw₁'_eq]

lemma heckeMulBasis_simple (C : CoxeterGroupData) (s : C.W) (hs : s ∈ C.simpleReflections) (w : C.W) :
    heckeMulBasis C s w = simpleReflMulBasis C s w := by
  have hs_ne : s ≠ 1 := C.simple_ne_one s hs
  rw [heckeMulBasis]
  simp only [hs_ne, ↓reduceDIte]
  rw [C.descentRefl_of_simple s hs, C.simple_sq s hs]
  rw [show heckeMulBasis C 1 w = Finsupp.single w 1 from by simp [heckeMulBasis]]
  rw [simpleActOnLinComb_single, one_smul]

lemma simpleReflMulBasis_apply (C : CoxeterGroupData) (s y w : C.W) :
    (simpleReflMulBasis C s y) w =
    if C.length (s * y) = C.length y + 1 then
      if s * y = w then 1 else 0
    else
      (if y = w then hecke_q - 1 else 0) + (if s * y = w then hecke_q else 0) := by
  simp only [simpleReflMulBasis, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> simp_all

lemma heckeMulBasis_descent (C : CoxeterGroupData) (w₁ : C.W) (hw₁ : w₁ ≠ 1) :
    heckeMulBasis C (C.descentRefl w₁) (C.descentRefl w₁ * w₁) = Finsupp.single w₁ 1 := by
  set s := C.descentRefl w₁
  set w₁' := s * w₁
  have hs : s ∈ C.simpleReflections := C.descentRefl_simple w₁ hw₁
  have hlen : C.length w₁' < C.length w₁ := C.descentRefl_length w₁ hw₁
  have sw₁'_eq : s * w₁' = w₁ := C.simple_cancel s hs w₁
  rw [heckeMulBasis_simple C s hs w₁']
  unfold simpleReflMulBasis
  rcases C.exchange_left s hs w₁' with h | h
  ·
    rw [if_pos h, sw₁'_eq]
  ·
    exfalso; rw [sw₁'_eq] at h; omega

lemma heckeMulBasis_unfold (C : CoxeterGroupData) (w₁ : C.W) (hw₁ : w₁ ≠ 1) (w₂ : C.W) :
    heckeMulBasis C w₁ w₂ =
    simpleActOnLinComb C (C.descentRefl w₁) (heckeMulBasis C (C.descentRefl w₁ * w₁) w₂) := by
  rw [heckeMulBasis]
  simp [hw₁]

lemma simpleActOnLinComb_add (C : CoxeterGroupData) (s : C.W)
    (f g : HeckeAlgebra C) :
    simpleActOnLinComb C s (f + g) =
    simpleActOnLinComb C s f + simpleActOnLinComb C s g := by
  unfold simpleActOnLinComb
  rw [Finsupp.sum_add_index' (fun w => by simp [zero_smul]) (fun w a₁ a₂ => by rw [add_smul])]

lemma simpleActOnLinComb_quadratic (C : CoxeterGroupData) (s : C.W)
    (hs : s ∈ C.simpleReflections) (w : C.W) :
    simpleActOnLinComb C s (simpleReflMulBasis C s w) =
    hecke_q • Finsupp.single w 1 + (hecke_q - 1) • simpleReflMulBasis C s w := by

  have hss : s * s = (1 : C.W) := C.simple_sq s hs
  have cancel : s * (s * w) = w := C.simple_cancel s hs w

  rcases C.exchange_left s hs w with hup | hdown
  ·

    have hdef : simpleReflMulBasis C s w = Finsupp.single (s * w) 1 := by
      unfold simpleReflMulBasis; rw [if_pos hup]
    rw [hdef]

    rw [simpleActOnLinComb_single, one_smul]


    have hdown_sw : ¬ (C.length (s * (s * w)) = C.length (s * w) + 1) := by
      rw [cancel]; omega
    unfold simpleReflMulBasis
    rw [if_neg hdown_sw, cancel]


    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [add_comm]
  ·

    have hdef : simpleReflMulBasis C s w = Finsupp.single w (hecke_q - 1) + Finsupp.single (s * w) hecke_q := by
      unfold simpleReflMulBasis
      rw [if_neg (by omega : ¬ (C.length (s * w) = C.length w + 1))]
    rw [hdef]

    rw [simpleActOnLinComb_add]

    rw [simpleActOnLinComb_single, simpleActOnLinComb_single]


    have hup_sw : C.length (s * (s * w)) = C.length (s * w) + 1 := by
      rw [cancel]; omega
    have hdef_sw : simpleReflMulBasis C s (s * w) = Finsupp.single w 1 := by
      unfold simpleReflMulBasis; rw [if_pos hup_sw, cancel]
    rw [hdef, hdef_sw]

    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [smul_add]
    simp only [Finsupp.smul_single, smul_eq_mul]


    ring_nf
    rw [add_comm]

lemma simpleActOnLinComb_smul (C : CoxeterGroupData) (s : C.W)
    (c : HeckeCoeffRing) (f : HeckeAlgebra C) :
    simpleActOnLinComb C s (c • f) = c • simpleActOnLinComb C s f := by
  unfold simpleActOnLinComb
  rw [Finsupp.sum_smul_index' (fun i => by simp [zero_smul])]
  rw [Finsupp.smul_sum]
  congr 1; ext1 w; ext1 d
  exact smul_assoc c d (simpleReflMulBasis C s w)

lemma heckeMulBasis_assoc_gen_rhs (C : CoxeterGroupData) (s : C.W)
    (hs : s ∈ C.simpleReflections) (w₂ w₃ : C.W) :
    (heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C s v) =
    simpleActOnLinComb C s (heckeMulBasis C w₂ w₃) := by
  unfold simpleActOnLinComb
  congr 1; ext1 v; ext1 c
  rw [heckeMulBasis_simple C s hs v]

lemma simpleActOnLinComb_quadratic_gen (C : CoxeterGroupData) (s : C.W)
    (hs : s ∈ C.simpleReflections) (f : HeckeAlgebra C) :
    simpleActOnLinComb C s (simpleActOnLinComb C s f) =
    (hecke_q - 1) • simpleActOnLinComb C s f + hecke_q • f := by
  induction f using Finsupp.induction_linear with
  | zero =>
    simp only [simpleActOnLinComb, Finsupp.sum_zero_index, smul_zero, add_zero]
  | add f g hf hg =>
    rw [simpleActOnLinComb_add, simpleActOnLinComb_add, hf, hg]
    rw [smul_add, smul_add]
    abel
  | single w c =>

    conv_lhs => rw [show Finsupp.single w c = c • Finsupp.single w 1 from
      by rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
    rw [simpleActOnLinComb_smul, simpleActOnLinComb_single, one_smul]

    rw [simpleActOnLinComb_smul]

    rw [simpleActOnLinComb_quadratic C s hs w]


    conv_rhs => rw [show Finsupp.single w c = c • Finsupp.single w 1 from
      by rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
    rw [simpleActOnLinComb_smul, simpleActOnLinComb_single, one_smul]
    rw [smul_add, smul_comm c (hecke_q - 1), smul_comm c hecke_q]
    rw [add_comm]

theorem heckeMulBasis_assoc_gen (C : CoxeterGroupData)
    (s : C.W) (hs : s ∈ C.simpleReflections) (w₂ w₃ : C.W) :
  (heckeMulBasis C s w₂).sum (fun v c => c • heckeMulBasis C v w₃) =
  (heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C s v) := by

  rw [heckeMulBasis_assoc_gen_rhs C s hs]

  rw [heckeMulBasis_simple C s hs w₂]

  induction hn : C.length w₂ using Nat.strongRecOn generalizing w₂ with
  | ind n ih =>

  by_cases hw₂ : w₂ = 1
  · subst hw₂
    have hup : C.length (s * 1) = C.length 1 + 1 := by
      rw [mul_one, C.length_simple s hs, C.length_one]
    have heval : simpleReflMulBasis C s 1 = Finsupp.single (s * 1) 1 := by
      unfold simpleReflMulBasis; rw [if_pos hup]
    rw [heval]
    rw [Finsupp.sum_single_index (by simp [zero_smul]), one_smul]
    rw [mul_one]
    rw [heckeMulBasis_one_left]
    rw [simpleActOnLinComb_single, one_smul]
    rw [heckeMulBasis_simple C s hs w₃]
  ·
    rcases C.exchange_left s hs w₂ with hup | hdown
    ·
      have heval : simpleReflMulBasis C s w₂ = Finsupp.single (s * w₂) 1 := by
        unfold simpleReflMulBasis; rw [if_pos hup]
      rw [heval]
      rw [Finsupp.sum_single_index (by simp [zero_smul]), one_smul]
      have hsw₂_ne : s * w₂ ≠ 1 := by
        intro h; have := C.length_one ▸ h ▸ hup; omega
      rw [heckeMulBasis_unfold C (s * w₂) hsw₂_ne w₃]
      rw [C.descentRefl_of_mul s hs w₂ hup]
      rw [C.simple_cancel s hs w₂]
    ·
      have hdown' : ¬ (C.length (s * w₂) = C.length w₂ + 1) := by omega
      have heval : simpleReflMulBasis C s w₂ =
          Finsupp.single w₂ (hecke_q - 1) + Finsupp.single (s * w₂) hecke_q := by
        unfold simpleReflMulBasis; rw [if_neg hdown']
      rw [heval]
      rw [Finsupp.sum_add_index' (fun w => by simp [zero_smul]) (fun w a₁ a₂ => by rw [add_smul])]
      rw [Finsupp.sum_single_index (by simp [zero_smul])]
      rw [Finsupp.sum_single_index (by simp [zero_smul])]
      have cancel : s * (s * w₂) = w₂ := C.simple_cancel s hs w₂
      have hup_sw₂ : C.length (s * (s * w₂)) = C.length (s * w₂) + 1 := by
        rw [cancel]; omega
      have heval_sw₂ : simpleReflMulBasis C s (s * w₂) = Finsupp.single (s * (s * w₂)) 1 := by
        unfold simpleReflMulBasis; rw [if_pos hup_sw₂]
      have ih_sw₂ : (simpleReflMulBasis C s (s * w₂)).sum (fun v c => c • heckeMulBasis C v w₃) =
          simpleActOnLinComb C s (heckeMulBasis C (s * w₂) w₃) :=
        ih (C.length (s * w₂)) (by omega) (s * w₂) rfl
      rw [heval_sw₂, cancel] at ih_sw₂
      rw [Finsupp.sum_single_index (by simp [zero_smul]), one_smul] at ih_sw₂

      set X := heckeMulBasis C (s * w₂) w₃
      rw [ih_sw₂]
      rw [simpleActOnLinComb_quadratic_gen C s hs X]


lemma finsupp_sum_comm_smul {W : Type*} {R : Type*} [CommRing R]
    (g : W → W →₀ R) (outer : W →₀ R) (inner : W → W →₀ R) :
    outer.sum (fun v c => c • (inner v).sum (fun u d => d • g u)) =
    (outer.sum (fun v c => c • inner v)).sum (fun u d => d • g u) := by
  rw [Finsupp.sum_sum_index (fun a => by simp [zero_smul]) (fun a b₁ b₂ => by rw [add_smul])]
  congr 1; ext1 v; ext1 c
  rw [Finsupp.sum_smul_index' (fun i => by simp [zero_smul])]
  rw [Finsupp.smul_sum]
  congr 1; ext1 i; ext1 d'
  exact (smul_assoc c d' (g i)).symm

theorem heckeMulBasis_assoc (C : CoxeterGroupData) (w₁ w₂ w₃ : C.W) :
  (heckeMulBasis C w₁ w₂).sum (fun v c => c • heckeMulBasis C v w₃) =
  (heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C w₁ v) := by

  induction hn : C.length w₁ using Nat.strongRecOn generalizing w₁ with
  | ind n ih =>
  by_cases hw₁ : w₁ = 1
  ·
    subst hw₁

    rw [heckeMulBasis_one_left]
    rw [Finsupp.sum_single_index (by simp [zero_smul])]
    rw [one_smul]


    symm
    have : ∀ v (c : HeckeCoeffRing), c • heckeMulBasis C 1 v = Finsupp.single v c := by
      intro v c; rw [heckeMulBasis_one_left, Finsupp.smul_single, smul_eq_mul, mul_one]
    simp_rw [this]
    exact Finsupp.sum_single _
  ·

    set s := C.descentRefl w₁
    set w₁' := s * w₁
    have hs : s ∈ C.simpleReflections := C.descentRefl_simple w₁ hw₁
    have hlen : C.length w₁' < C.length w₁ := C.descentRefl_length w₁ hw₁
    have hdescent : heckeMulBasis C s w₁' = Finsupp.single w₁ 1 :=
      heckeMulBasis_descent C w₁ hw₁


    have hw₁_expand : ∀ w : C.W, heckeMulBasis C w₁ w =
        (heckeMulBasis C w₁' w).sum (fun v c => c • heckeMulBasis C s v) := by
      intro w
      have := heckeMulBasis_assoc_gen C s hs w₁' w
      rw [hdescent, Finsupp.sum_single_index (by simp [zero_smul]), one_smul] at this
      exact this

    have ih_w₁' :
        (heckeMulBasis C w₁' w₂).sum (fun v c => c • heckeMulBasis C v w₃) =
        (heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C w₁' v) :=
      ih (C.length w₁') (by omega) w₁' rfl

    calc (heckeMulBasis C w₁ w₂).sum (fun v c => c • heckeMulBasis C v w₃)

        _ = ((heckeMulBasis C w₁' w₂).sum (fun v c => c • heckeMulBasis C s v)).sum
              (fun u d => d • heckeMulBasis C u w₃) := by
            rw [hw₁_expand w₂]

        _ = (heckeMulBasis C w₁' w₂).sum (fun v c =>
              c • (heckeMulBasis C s v).sum (fun u d => d • heckeMulBasis C u w₃)) := by
            rw [← finsupp_sum_comm_smul (fun u => heckeMulBasis C u w₃)
                  (heckeMulBasis C w₁' w₂) (fun v => heckeMulBasis C s v)]

        _ = (heckeMulBasis C w₁' w₂).sum (fun v c =>
              c • (heckeMulBasis C v w₃).sum (fun u d => d • heckeMulBasis C s u)) := by
            simp_rw [heckeMulBasis_assoc_gen C s hs]

        _ = ((heckeMulBasis C w₁' w₂).sum (fun v c => c • heckeMulBasis C v w₃)).sum
              (fun u d => d • heckeMulBasis C s u) := by
            rw [finsupp_sum_comm_smul (fun u => heckeMulBasis C s u)
                  (heckeMulBasis C w₁' w₂) (fun v => heckeMulBasis C v w₃)]

        _ = ((heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C w₁' v)).sum
              (fun u d => d • heckeMulBasis C s u) := by
            rw [ih_w₁']

        _ = (heckeMulBasis C w₂ w₃).sum (fun v c =>
              c • (heckeMulBasis C w₁' v).sum (fun u d => d • heckeMulBasis C s u)) := by
            rw [← finsupp_sum_comm_smul (fun u => heckeMulBasis C s u)
                  (heckeMulBasis C w₂ w₃) (fun v => heckeMulBasis C w₁' v)]

        _ = (heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C w₁ v) := by
            congr 1; ext1 v; ext1 c; rw [hw₁_expand v]

instance HeckeAlgebra.instRing (C : CoxeterGroupData) : Ring (HeckeAlgebra C) where
  __ := HeckeAlgebra.instAddCommGroup C
  mul := heckeMul C
  one := Finsupp.single 1 1
  mul_assoc := by
    intro a b c
    show heckeMul C (heckeMul C a b) c = heckeMul C a (heckeMul C b c)

    have hzl : ∀ (g : HeckeAlgebra C), heckeMul C 0 g = 0 :=
      fun _ => Finsupp.sum_zero_index
    have hzr : ∀ (f : HeckeAlgebra C), heckeMul C f 0 = 0 := by
      intro f; unfold heckeMul
      have : ∀ (w₁ : C.W) (a₁ : HeckeCoeffRing),
        Finsupp.sum (0 : HeckeAlgebra C) (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) = 0 :=
        fun _ _ => Finsupp.sum_zero_index
      conv_lhs => arg 2; ext w₁ a₁; rw [this w₁ a₁]
      simp [Finsupp.sum]
    have hal : ∀ (f g h : HeckeAlgebra C),
        heckeMul C (f + g) h = heckeMul C f h + heckeMul C g h := by
      intro f g h; unfold heckeMul
      apply Finsupp.sum_add_index'
      · intro i; show h.sum (fun w₂ a₂ => (0 * a₂) • heckeMulBasis C i w₂) = 0
        simp [zero_mul, zero_smul, Finsupp.sum]
      · intro i b₁ b₂
        conv_lhs => arg 2; ext w₂ a₂; rw [add_mul, add_smul]
        rw [← Finsupp.sum_add]
    have har : ∀ (f g h : HeckeAlgebra C),
        heckeMul C f (g + h) = heckeMul C f g + heckeMul C f h := by
      intro f g h; unfold heckeMul
      have inner_split : ∀ w₁ a₁,
        (g + h).sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) =
        g.sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) +
        h.sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) := by
        intro w₁ a₁
        apply Finsupp.sum_add_index'
        · intro i; simp
        · intro i b₁ b₂; rw [mul_add, add_smul]
      conv_lhs => arg 2; ext w₁ a₁; rw [inner_split w₁ a₁]
      rw [← Finsupp.sum_add]

    apply @Finsupp.induction_linear C.W HeckeCoeffRing _
      (fun a => heckeMul C (heckeMul C a b) c = heckeMul C a (heckeMul C b c)) a
    ·
      rw [hzl, hzl, hzl]
    ·
      intro a₁ a₂ h₁ h₂
      rw [hal, hal, h₁, h₂, ← hal]
    ·
      intro w₁ r₁
      apply @Finsupp.induction_linear C.W HeckeCoeffRing _
        (fun b => heckeMul C (heckeMul C (Finsupp.single w₁ r₁) b) c =
                  heckeMul C (Finsupp.single w₁ r₁) (heckeMul C b c)) b
      ·
        rw [hzr, hzl, hzr]
      ·
        intro b₁ b₂ h₁ h₂
        rw [har, hal, h₁, h₂, ← har]; congr 1; rw [← hal]
      ·
        intro w₂ r₂
        apply @Finsupp.induction_linear C.W HeckeCoeffRing _
          (fun c => heckeMul C (heckeMul C (Finsupp.single w₁ r₁) (Finsupp.single w₂ r₂)) c =
                    heckeMul C (Finsupp.single w₁ r₁) (heckeMul C (Finsupp.single w₂ r₂) c)) c
        ·
          rw [hzr, hzr, hzr]
        ·
          intro c₁ c₂ h₁ h₂
          rw [har, h₁, har, h₂, ← har]
        ·
          intro w₃ r₃


          have hss12 : heckeMul C (Finsupp.single w₁ r₁) (Finsupp.single w₂ r₂) =
              (r₁ * r₂) • heckeMulBasis C w₁ w₂ := by
            unfold heckeMul
            rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
            rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]
          have hss23 : heckeMul C (Finsupp.single w₂ r₂) (Finsupp.single w₃ r₃) =
              (r₂ * r₃) • heckeMulBasis C w₂ w₃ := by
            unfold heckeMul
            rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
            rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]
          rw [hss12, hss23]


          show heckeMul C ((r₁ * r₂) • heckeMulBasis C w₁ w₂) (Finsupp.single w₃ r₃) =
               heckeMul C (Finsupp.single w₁ r₁) ((r₂ * r₃) • heckeMulBasis C w₂ w₃)

          have hml : ∀ (f : HeckeAlgebra C) (w : C.W) (r : HeckeCoeffRing),
              heckeMul C f (Finsupp.single w r) =
              f.sum (fun v d => (d * r) • heckeMulBasis C v w) := by
            intro f w r; unfold heckeMul; congr 1; ext v d
            rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]

          have hmr : ∀ (w : C.W) (r : HeckeCoeffRing) (g : HeckeAlgebra C),
              heckeMul C (Finsupp.single w r) g =
              g.sum (fun v d => (r * d) • heckeMulBasis C w v) := by
            intro w r g; unfold heckeMul
            rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]

          rw [hml, hmr]


          have key : ∀ (b : HeckeCoeffRing) (g : HeckeAlgebra C)
              (h : C.W → HeckeCoeffRing → HeckeAlgebra C) (h0 : ∀ i, h i 0 = 0),
              (b • g).sum h = g.sum (fun i cc => h i (b • cc)) :=
            fun b g h h0 => Finsupp.sum_smul_index' h0
          rw [key (r₁ * r₂) (heckeMulBasis C w₁ w₂)
              (fun v d => (d * r₃) • heckeMulBasis C v w₃)
              (fun i => by simp [zero_mul, zero_smul])]
          rw [key (r₂ * r₃) (heckeMulBasis C w₂ w₃)
              (fun v d => (r₁ * d) • heckeMulBasis C w₁ v)
              (fun i => by simp [mul_zero, zero_smul])]

          simp_rw [smul_eq_mul]

          conv_lhs => arg 2; ext v d; rw [show (r₁ * r₂) * d * r₃ = (r₁ * r₂ * r₃) * d by ring, mul_smul]
          conv_rhs => arg 2; ext v d; rw [show r₁ * ((r₂ * r₃) * d) = (r₁ * r₂ * r₃) * d by ring, mul_smul]
          rw [← Finsupp.smul_sum, ← Finsupp.smul_sum]
          congr 1
          exact heckeMulBasis_assoc C w₁ w₂ w₃

  one_mul := by
    intro b
    show heckeMul C (Finsupp.single 1 1) b = b
    unfold heckeMul
    rw [Finsupp.sum_single_index]
    · have key : (fun w₂ a₂ => (1 * a₂) • heckeMulBasis C 1 w₂) =
                 (fun w₂ (a₂ : HeckeCoeffRing) => (Finsupp.single w₂ a₂ : HeckeAlgebra C)) := by
        ext w₂ a₂ : 2
        simp only [one_mul]
        have hb : heckeMulBasis C 1 w₂ = Finsupp.single w₂ 1 :=
          heckeMulBasis_one_left C w₂
        rw [hb]
        change (a₂ • (Finsupp.single w₂ 1 : C.W →₀ HeckeCoeffRing) : C.W →₀ HeckeCoeffRing) =
               (Finsupp.single w₂ a₂ : C.W →₀ HeckeCoeffRing)
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [key]
      exact Finsupp.sum_single _
    · simp [zero_mul, zero_smul, Finsupp.sum]
  mul_one := by
    intro b
    show heckeMul C b (Finsupp.single 1 1) = b
    unfold heckeMul
    have inner_simp : ∀ w₁ (a₁ : HeckeCoeffRing),
      (Finsupp.single (1 : C.W) (1 : HeckeCoeffRing)).sum
        (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) =
      Finsupp.single w₁ a₁ := by
      intro w₁ a₁
      rw [Finsupp.sum_single_index]
      · rw [mul_one]
        have hb : heckeMulBasis C w₁ 1 = Finsupp.single w₁ 1 :=
          heckeMulBasis_one_right C w₁
        rw [hb]
        change (a₁ • (Finsupp.single w₁ 1 : C.W →₀ HeckeCoeffRing) : C.W →₀ HeckeCoeffRing) =
               (Finsupp.single w₁ a₁ : C.W →₀ HeckeCoeffRing)
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      · simp [mul_zero, zero_smul]
    have key : (fun w₁ a₁ =>
      (Finsupp.single (1 : C.W) (1 : HeckeCoeffRing)).sum
        (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂)) =
      (fun w₁ (a₁ : HeckeCoeffRing) => (Finsupp.single w₁ a₁ : HeckeAlgebra C)) := by
      ext w₁ a₁ : 2
      exact inner_simp w₁ a₁
    rw [key]
    exact Finsupp.sum_single _
  left_distrib := by
    intro f g h
    show heckeMul C f (g + h) = heckeMul C f g + heckeMul C f h
    unfold heckeMul
    have inner_split : ∀ w₁ a₁,
      (g + h).sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) =
      g.sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) +
      h.sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) := by
      intro w₁ a₁
      apply Finsupp.sum_add_index'
      · intro i; simp
      · intro i b₁ b₂; rw [mul_add, add_smul]
    conv_lhs => arg 2; ext w₁ a₁; rw [inner_split w₁ a₁]
    rw [← Finsupp.sum_add]
  right_distrib := by
    intro f g h
    show heckeMul C (f + g) h = heckeMul C f h + heckeMul C g h
    unfold heckeMul
    apply Finsupp.sum_add_index'
    · intro i
      show h.sum (fun w₂ a₂ => (0 * a₂) • heckeMulBasis C i w₂) = 0
      simp [zero_mul, zero_smul, Finsupp.sum]
    · intro i b₁ b₂
      conv_lhs => arg 2; ext w₂ a₂; rw [add_mul, add_smul]
      rw [← Finsupp.sum_add]
  zero_mul := by
    intro g
    show heckeMul C 0 g = 0
    unfold heckeMul
    exact Finsupp.sum_zero_index
  mul_zero := by
    intro f
    show heckeMul C f 0 = 0
    unfold heckeMul
    have : ∀ (w₁ : C.W) (a₁ : HeckeCoeffRing),
      Finsupp.sum (0 : HeckeAlgebra C) (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) = 0 :=
      fun _ _ => Finsupp.sum_zero_index
    conv_lhs => arg 2; ext w₁ a₁; rw [this w₁ a₁]
    simp [Finsupp.sum]
  natCast n := Finsupp.single 1 (n : HeckeCoeffRing)
  natCast_zero := by
    change Finsupp.single (1 : C.W) ((0 : ℕ) : HeckeCoeffRing) = 0
    simp
  natCast_succ := by
    intro n
    change Finsupp.single (1 : C.W) ((n + 1 : ℕ) : HeckeCoeffRing) =
      Finsupp.single (1 : C.W) ((n : ℕ) : HeckeCoeffRing) + Finsupp.single (1 : C.W) (1 : HeckeCoeffRing)
    rw [← Finsupp.single_add]
    congr 1
    push_cast
    ring
  intCast n := Finsupp.single 1 (n : HeckeCoeffRing)
  intCast_ofNat := by
    intro n
    change Finsupp.single (1 : C.W) ((↑n : ℤ) : HeckeCoeffRing) =
      Finsupp.single (1 : C.W) ((n : ℕ) : HeckeCoeffRing)
    simp [Int.cast_natCast]
  intCast_negSucc := by
    intro n
    change Finsupp.single (1 : C.W) ((Int.negSucc n : ℤ) : HeckeCoeffRing) =
      -Finsupp.single (1 : C.W) ((n + 1 : ℕ) : HeckeCoeffRing)
    ext w
    simp only [Finsupp.single_apply, Finsupp.neg_apply]
    split
    · simp [Int.negSucc_eq, Int.cast_neg, Int.cast_natCast, Nat.cast_succ]
    · simp

def HeckeAlgebra.ofScalar (C : CoxeterGroupData) (a : HeckeCoeffRing) : HeckeAlgebra C :=
  Finsupp.single 1 a

def heckeAlgebraMap (C : CoxeterGroupData) : HeckeCoeffRing →+* HeckeAlgebra C where
  toFun r := Finsupp.single 1 r
  map_one' := rfl
  map_mul' := by
    intro a b
    show Finsupp.single (1 : C.W) (a * b) = heckeMul C (Finsupp.single 1 a) (Finsupp.single 1 b)
    unfold heckeMul
    rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
    rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]
    have hb : heckeMulBasis C 1 1 = Finsupp.single (1 : C.W) 1 := by
      unfold heckeMulBasis
      simp [C.length_one]
    rw [hb, Finsupp.smul_single, smul_eq_mul, mul_one]
  map_zero' := by
    change Finsupp.single (1 : C.W) (0 : HeckeCoeffRing) = 0
    simp
  map_add' := by
    intro a b
    change Finsupp.single (1 : C.W) (a + b) =
      Finsupp.single (1 : C.W) a + Finsupp.single (1 : C.W) b
    rw [Finsupp.single_add]

instance HeckeAlgebra.instAlgebra (C : CoxeterGroupData) :
    Algebra HeckeCoeffRing (HeckeAlgebra C) where
  __ := HeckeAlgebra.instModule C
  algebraMap := heckeAlgebraMap C
  commutes' := by
    intro r x

    show heckeMul C (Finsupp.single 1 r) x = heckeMul C x (Finsupp.single 1 r)

    apply @Finsupp.induction_linear C.W HeckeCoeffRing _
      (fun x => heckeMul C (Finsupp.single 1 r) x = heckeMul C x (Finsupp.single 1 r)) x
    ·
      simp only [show heckeMul C (Finsupp.single 1 r) 0 = 0 from by
        unfold heckeMul; have : ∀ (w₁ : C.W) (a₁ : HeckeCoeffRing),
          Finsupp.sum (0 : HeckeAlgebra C) (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) = 0 :=
          fun _ _ => Finsupp.sum_zero_index
        rw [Finsupp.sum_single_index (by simp [zero_smul, Finsupp.sum])]

        simp [this]]
      simp only [show heckeMul C 0 (Finsupp.single 1 r) = 0 from Finsupp.sum_zero_index]
    ·
      intro x₁ x₂ h₁ h₂
      have hleft : ∀ (f g : HeckeAlgebra C),
          heckeMul C (Finsupp.single 1 r) (f + g) =
          heckeMul C (Finsupp.single 1 r) f + heckeMul C (Finsupp.single 1 r) g := by
        intro f g; unfold heckeMul
        rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
        rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
        rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
        apply Finsupp.sum_add_index'
        · intro i; simp
        · intro i b₁ b₂; rw [mul_add, add_smul]
      have hright : ∀ (f g : HeckeAlgebra C),
          heckeMul C (f + g) (Finsupp.single 1 r) =
          heckeMul C f (Finsupp.single 1 r) + heckeMul C g (Finsupp.single 1 r) := by
        intro f g; unfold heckeMul
        apply Finsupp.sum_add_index'
        · intro i
          show (Finsupp.single 1 r).sum (fun w₂ a₂ => (0 * a₂) • heckeMulBasis C i w₂) = 0
          simp [zero_mul, zero_smul, Finsupp.sum]
        · intro i b₁ b₂
          conv_lhs => arg 2; ext w₂ a₂; rw [add_mul, add_smul]
          rw [← Finsupp.sum_add]
      rw [hleft, h₁, h₂, hright]
    ·
      intro w a

      have lhs_eq : heckeMul C (Finsupp.single 1 r) (Finsupp.single w a) =
          Finsupp.single w (r * a) := by
        unfold heckeMul
        rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
        rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]
        have hb : heckeMulBasis C 1 w = Finsupp.single w 1 := by
          unfold heckeMulBasis; simp [C.length_one]
        rw [hb, Finsupp.smul_single, smul_eq_mul, mul_one]

      have rhs_eq : heckeMul C (Finsupp.single w a) (Finsupp.single 1 r) =
          Finsupp.single w (a * r) := by
        unfold heckeMul
        rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
        rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]
        have hb : heckeMulBasis C w 1 = Finsupp.single w 1 :=
          heckeMulBasis_one_right C w
        rw [hb, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [lhs_eq, rhs_eq]
      congr 1
      exact mul_comm r a
  smul_def' := by
    intro r x

    show r • x = heckeMul C (Finsupp.single 1 r) x
    apply @Finsupp.induction_linear C.W HeckeCoeffRing _
      (fun x => r • x = heckeMul C (Finsupp.single 1 r) x) x
    ·
      simp only [smul_zero]
      unfold heckeMul
      rw [Finsupp.sum_single_index (by simp [zero_smul, Finsupp.sum])]

      simp [Finsupp.sum]
    ·
      intro x₁ x₂ h₁ h₂
      rw [smul_add, h₁, h₂]

      unfold heckeMul
      rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
      rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
      rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
      symm
      apply Finsupp.sum_add_index'
      · intro i; simp
      · intro i b₁ b₂; rw [mul_add, add_smul]
    ·
      intro w a
      rw [Finsupp.smul_single, smul_eq_mul]
      unfold heckeMul
      rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
      rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]
      have hb : heckeMulBasis C 1 w = Finsupp.single w 1 := by
        unfold heckeMulBasis; simp [C.length_one]
      rw [hb, Finsupp.smul_single, smul_eq_mul, mul_one]

lemma heckeMul_single_single (C : CoxeterGroupData) (w₁ w₂ : C.W) (r₁ r₂ : HeckeCoeffRing) :
    heckeMul C (Finsupp.single w₁ r₁) (Finsupp.single w₂ r₂) =
    (r₁ * r₂) • heckeMulBasis C w₁ w₂ := by
  unfold heckeMul
  rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
  rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]

lemma heckeMul_add_left (C : CoxeterGroupData) (f₁ f₂ g : HeckeAlgebra C) :
    heckeMul C (f₁ + f₂) g = heckeMul C f₁ g + heckeMul C f₂ g := by
  unfold heckeMul
  apply Finsupp.sum_add_index'
  · intro i; show g.sum (fun w₂ a₂ => (0 * a₂) • heckeMulBasis C i w₂) = 0
    simp [zero_mul, zero_smul, Finsupp.sum]
  · intro i b₁ b₂
    conv_lhs => arg 2; ext w₂ a₂; rw [add_mul, add_smul]
    rw [← Finsupp.sum_add]

lemma heckeMul_add_right (C : CoxeterGroupData) (f g₁ g₂ : HeckeAlgebra C) :
    heckeMul C f (g₁ + g₂) = heckeMul C f g₁ + heckeMul C f g₂ := by
  unfold heckeMul
  have inner_split : ∀ w₁ a₁,
    (g₁ + g₂).sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) =
    g₁.sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) +
    g₂.sum (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) := by
    intro w₁ a₁
    apply Finsupp.sum_add_index'
    · intro i; simp
    · intro i b₁ b₂; rw [mul_add, add_smul]
  conv_lhs => arg 2; ext w₁ a₁; rw [inner_split w₁ a₁]
  rw [← Finsupp.sum_add]

def heckeStdBasis (C : CoxeterGroupData) :
    Module.Basis C.W HeckeCoeffRing (HeckeAlgebra C) :=
  Finsupp.basisSingleOne

abbrev hecke_std_basis := heckeStdBasis

theorem heckeStdBasis_eq_T (C : CoxeterGroupData) (w : C.W) :
    heckeStdBasis C w = HeckeAlgebra.T C w := by
  show Finsupp.basisSingleOne w = Finsupp.single w 1
  simp [Finsupp.basisSingleOne]

theorem heckeStdBasis_coe_eq_T (C : CoxeterGroupData) :
    (heckeStdBasis C : C.W → HeckeAlgebra C) = HeckeAlgebra.T C :=
  funext (heckeStdBasis_eq_T C)

theorem hecke_basis (C : CoxeterGroupData) :
    LinearIndependent HeckeCoeffRing (HeckeAlgebra.T C) ∧
    Submodule.span HeckeCoeffRing (Set.range (HeckeAlgebra.T C)) = ⊤ := by
  have hcoe := heckeStdBasis_coe_eq_T C
  exact ⟨hcoe ▸ (heckeStdBasis C).linearIndependent, hcoe ▸ (heckeStdBasis C).span_eq⟩

theorem hecke_basis_injective (C : CoxeterGroupData) :
    Function.Injective (HeckeAlgebra.T C) :=
  (hecke_basis C).1.injective

def coeffInvolution : HeckeCoeffRing → HeckeCoeffRing :=
  Finsupp.mapDomain (fun (n : ℤ) => -n)

theorem coeffInvolution_involutive : Function.Involutive coeffInvolution := by
  intro x
  simp only [coeffInvolution]
  rw [← Finsupp.mapDomain_comp]
  simp [Finsupp.mapDomain_id]

theorem coeffInvolution_T (n : ℤ) :
    coeffInvolution (LaurentPolynomial.T n) = LaurentPolynomial.T (-n) := by
  unfold coeffInvolution LaurentPolynomial.T
  rw [Finsupp.mapDomain_single]

def negAddHom : ℤ →+ ℤ where
  toFun n := -n
  map_zero' := by simp
  map_add' := by intros; simp [neg_add_rev, add_comm]

def coeffInvolutionRingHom : HeckeCoeffRing →+* HeckeCoeffRing :=
  AddMonoidAlgebra.mapDomainRingHom ℤ negAddHom

theorem coeffInvolution_eq_ringHom (a : HeckeCoeffRing) :
    coeffInvolution a = coeffInvolutionRingHom a := by
  simp [coeffInvolution, coeffInvolutionRingHom, AddMonoidAlgebra.mapDomainRingHom,
        AddMonoidAlgebra.mapDomain, negAddHom]

theorem coeffInvolution_mul (a b : HeckeCoeffRing) :
    coeffInvolution (a * b) = coeffInvolution a * coeffInvolution b := by
  rw [coeffInvolution_eq_ringHom, coeffInvolution_eq_ringHom, coeffInvolution_eq_ringHom]
  exact map_mul coeffInvolutionRingHom a b

theorem coeffInvolution_zero : coeffInvolution 0 = 0 := by
  rw [coeffInvolution_eq_ringHom]; exact map_zero coeffInvolutionRingHom

theorem coeffInvolution_add (a b : HeckeCoeffRing) :
    coeffInvolution (a + b) = coeffInvolution a + coeffInvolution b := by
  unfold coeffInvolution
  exact Finsupp.mapDomain_add

def RPoly (C : CoxeterGroupData) (x y : C.W) : Polynomial ℤ :=
  if hy : y = 1 then (if x = 1 then 1 else 0)
  else
    let s := C.descentRefl y
    let sy := s * y
    let sx := s * x
    if C.length sx < C.length x then
      RPoly C sx sy
    else
      (Polynomial.X - Polynomial.C 1) * RPoly C x sy + Polynomial.X * RPoly C sx sy
termination_by C.length y
decreasing_by all_goals exact C.descentRefl_length y hy

def polyEvalQInv (p : Polynomial ℤ) : HeckeCoeffRing :=
  p.eval₂ (Int.castRingHom (LaurentPolynomial ℤ)) (LaurentPolynomial.T (-2))

def D_on_basis (C : CoxeterGroupData) (w : C.W) : HeckeAlgebra C :=
  ∑ x : C.W, Finsupp.single x
    (LaurentPolynomial.T (-(2 * (C.length x : ℤ))) * polyEvalQInv (RPoly C x w))

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in
def HeckeAlgebra.D (C : CoxeterGroupData) : HeckeAlgebra C → HeckeAlgebra C :=
  fun h => h.sum fun w aw => coeffInvolution aw • D_on_basis C w

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in
lemma HeckeAlgebra.D_zero (C : CoxeterGroupData) :
    HeckeAlgebra.D C 0 = 0 := by
  unfold HeckeAlgebra.D
  exact Finsupp.sum_zero_index

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in
lemma HeckeAlgebra.D_add (C : CoxeterGroupData)
    (f g : HeckeAlgebra C) :
    HeckeAlgebra.D C (f + g) = HeckeAlgebra.D C f + HeckeAlgebra.D C g := by
  show (f + g).sum (fun w aw => coeffInvolution aw • D_on_basis C w) =
    f.sum (fun w aw => coeffInvolution aw • D_on_basis C w) +
    g.sum (fun w aw => coeffInvolution aw • D_on_basis C w)
  apply Finsupp.sum_add_index'
  · intro i; simp [coeffInvolution_zero]
  · intro i b₁ b₂
    show coeffInvolution (b₁ + b₂) • D_on_basis C i =
      coeffInvolution b₁ • D_on_basis C i + coeffInvolution b₂ • D_on_basis C i
    rw [coeffInvolution_add, add_smul]

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in
lemma HeckeAlgebra.D_single (C : CoxeterGroupData) (w : C.W) (c : HeckeCoeffRing) :
    HeckeAlgebra.D C (Finsupp.single w c) = coeffInvolution c • D_on_basis C w := by
  unfold HeckeAlgebra.D
  rw [Finsupp.sum_single_index]
  simp [coeffInvolution_zero]

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in
theorem HeckeAlgebra.D_semilinear (C : CoxeterGroupData)
    (a : HeckeCoeffRing) (h : HeckeAlgebra C) :
    HeckeAlgebra.D C (a • h) = coeffInvolution a • HeckeAlgebra.D C h := by
  unfold HeckeAlgebra.D
  calc Finsupp.sum (a • h) (fun w aw => coeffInvolution aw • D_on_basis C w)
      = Finsupp.sum h (fun i c => coeffInvolution (a • c) • D_on_basis C i) := by
          exact Finsupp.sum_smul_index' (fun i => by simp [coeffInvolution_zero])
    _ = Finsupp.sum h (fun i c => coeffInvolution a • (coeffInvolution c • D_on_basis C i)) := by
          congr 1; ext i c; rw [show a • c = a * c from rfl, coeffInvolution_mul, mul_smul]
    _ = coeffInvolution a • Finsupp.sum h (fun w aw => coeffInvolution aw • D_on_basis C w) := by
          rw [← Finsupp.smul_sum]

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in
noncomputable def HeckeAlgebra.D_addHom (C : CoxeterGroupData) :
    HeckeAlgebra C →+ HeckeAlgebra C where
  toFun := HeckeAlgebra.D C
  map_zero' := HeckeAlgebra.D_zero C
  map_add' := HeckeAlgebra.D_add C

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in
lemma HeckeAlgebra.D_finset_sum (C : CoxeterGroupData) {ι : Type*}
    (s : Finset ι) (f : ι → HeckeAlgebra C) :
    HeckeAlgebra.D C (∑ i ∈ s, f i) = ∑ i ∈ s, HeckeAlgebra.D C (f i) :=
  map_sum (HeckeAlgebra.D_addHom C) f s

noncomputable def D_coeff (C : CoxeterGroupData) (x w : C.W) : HeckeCoeffRing :=
  LaurentPolynomial.T (-(2 * (C.length x : ℤ))) * polyEvalQInv (RPoly C x w)

lemma finset_sum_single {α : Type*} [DecidableEq α] {β : Type*} [AddCommMonoid β]
    {ι : Type*} (s : Finset ι) (y : α) (f : ι → β) :
    ∑ i ∈ s, Finsupp.single y (f i) = Finsupp.single y (∑ i ∈ s, f i) :=
  (map_sum (Finsupp.singleAddHom y) f s).symm

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in
lemma smul_D_on_basis (C : CoxeterGroupData) (c : HeckeCoeffRing) (x : C.W) :
    c • D_on_basis C x = ∑ y : C.W, Finsupp.single y (c * D_coeff C y x) := by
  show c • (∑ z : C.W, Finsupp.single z (D_coeff C z x)) = _
  rw [Finset.smul_sum]
  congr 1; ext y
  rw [Finsupp.smul_single, smul_eq_mul]

lemma RPoly_unfold_lt (C : CoxeterGroupData) (x y : C.W) (hy : y ≠ 1)
    (hlt : C.length (C.descentRefl y * x) < C.length x) :
    RPoly C x y = RPoly C (C.descentRefl y * x) (C.descentRefl y * y) := by
  conv_lhs => rw [RPoly]
  simp only [dif_neg hy]
  simp only [hlt, ite_true]

lemma RPoly_unfold_ge (C : CoxeterGroupData) (x y : C.W) (hy : y ≠ 1)
    (hge : ¬ C.length (C.descentRefl y * x) < C.length x) :
    RPoly C x y = (Polynomial.X - Polynomial.C 1) * RPoly C x (C.descentRefl y * y) +
      Polynomial.X * RPoly C (C.descentRefl y * x) (C.descentRefl y * y) := by
  conv_lhs => rw [RPoly]
  simp only [dif_neg hy]
  simp only [hge, ite_false]


lemma sum_single_ite_eq (C : CoxeterGroupData) (w : C.W) :
    ∑ y : C.W, Finsupp.single y (if y = w then (1 : HeckeCoeffRing) else 0) =
    Finsupp.single w 1 := by
  have : ∀ y : C.W, Finsupp.single y (if y = w then (1 : HeckeCoeffRing) else 0) =
    if y = w then Finsupp.single y 1 else 0 := by
    intro y
    split_ifs with h
    · rfl
    · exact (Finsupp.single_zero (a := y) : Finsupp.single y (0 : HeckeCoeffRing) = 0)
  simp_rw [this]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_univ]


attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

def mkBoundedPoly (bound : ℕ) (coeffs : ℕ → ℤ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range (bound + 1), Polynomial.C (coeffs i) * Polynomial.X ^ i

lemma mkBoundedPoly_natDegree_le (bound : ℕ) (coeffs : ℕ → ℤ) :
    (mkBoundedPoly bound coeffs).natDegree ≤ bound := by
  unfold mkBoundedPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  calc (Polynomial.C (coeffs i) * Polynomial.X ^ i).natDegree
      ≤ i := Polynomial.natDegree_C_mul_X_pow_le (coeffs i) i
    _ ≤ bound := by rw [Finset.mem_range] at hi; omega

lemma poly_eq_mkBoundedPoly_of_deg_le (p : Polynomial ℤ) (bound : ℕ)
    (hdeg : p.natDegree ≤ bound) :
    p = mkBoundedPoly bound (fun j => p.coeff j) := by
  unfold mkBoundedPoly
  conv_lhs => rw [p.as_sum_range' (bound + 1) (by omega)]
  congr 1; ext i
  simp only [Polynomial.coeff_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    mul_ite, mul_one, mul_zero]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

lemma mkBoundedPoly_congr (bound : ℕ) (f g : ℕ → ℤ)
    (h : ∀ j, j ≤ bound → f j = g j) :
    mkBoundedPoly bound f = mkBoundedPoly bound g := by
  simp only [mkBoundedPoly]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [h i (by omega)]

def middleCoeffs (C : CoxeterGroupData) (y _w : C.W)
    (rec_val : C.W → Polynomial ℤ) : Polynomial ℤ :=
  ∑ z : C.W, Polynomial.C ((-1 : ℤ) ^ (C.length y + C.length z)) * RPoly C y z * rec_val z

def self_dual_coeffs (C : CoxeterGroupData) (y w : C.W)
    (_bound : ℕ) (rec_val : C.W → Polynomial ℤ) : ℕ → ℤ :=
  fun (j : ℕ) => (middleCoeffs C y w rec_val).coeff j

def KazhdanLusztigPoly (C : CoxeterGroupData) (y w : C.W) : Polynomial ℤ :=
  if ¬ C.bruhatLE y w then 0
  else if y = w then 1
  else
    let bound := (C.length w - C.length y - 1) / 2
    let rec_val : C.W → Polynomial ℤ := fun z =>
      if _h : C.bruhatLE y z ∧ z ≠ y ∧ C.bruhatLE z w then
        KazhdanLusztigPoly C z w
      else 0
    mkBoundedPoly bound (self_dual_coeffs C y w bound rec_val)
termination_by C.length w - C.length y
decreasing_by
  have hyz : C.bruhatLE y z := _h.1
  have hzy : z ≠ y := _h.2.1
  have hzw : C.bruhatLE z w := _h.2.2
  have : C.length y < C.length z := C.bruhat_length_strict y z hyz (Ne.symm hzy)
  have : C.length z ≤ C.length w := C.bruhat_length_le z w hzw
  omega

theorem kl_poly_zero_unless_bruhat_le (C : CoxeterGroupData) (y w : C.W) :
  ¬ C.bruhatLE y w → KazhdanLusztigPoly C y w = 0 := by
  intro h
  unfold KazhdanLusztigPoly
  simp [h]

theorem kl_poly_diag (C : CoxeterGroupData) (w : C.W) :
  KazhdanLusztigPoly C w w = 1 := by
  unfold KazhdanLusztigPoly
  simp [C.bruhat_refl w]


structure CoxeterWeylCompatibility
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (C : CoxeterGroupData)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) where
  ι : C.W ≃* wg.W



def IsDominantRegularWeight
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=

  IsDominantWeightLE rd wg lam ∧

  (∀ w : wg.W, wg.shiftedAction w lam = lam → w = 1)



def polyToHeckeCoeff (p : Polynomial ℤ) : HeckeCoeffRing :=
  p.eval₂ (Int.castRingHom (LaurentPolynomial ℤ)) (LaurentPolynomial.T 2)

def KLBasisElement (C : CoxeterGroupData) (w : C.W) : HeckeAlgebra C :=
  ∑ y : C.W, Finsupp.single y
    (LaurentPolynomial.T (-(C.length w : ℤ)) * polyToHeckeCoeff (KazhdanLusztigPoly C y w))


attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

lemma klp_unfold (C : CoxeterGroupData) (y w : C.W)
    (hle : C.bruhatLE y w) (hne : y ≠ w) :
    KazhdanLusztigPoly C y w = mkBoundedPoly ((C.length w - C.length y - 1) / 2)
      (self_dual_coeffs C y w ((C.length w - C.length y - 1) / 2)
        (fun z => if C.bruhatLE y z ∧ z ≠ y ∧ C.bruhatLE z w then
          KazhdanLusztigPoly C z w else 0)) := by
  conv_lhs => rw [KazhdanLusztigPoly]
  simp only [hle, hne, ite_false, not_true_eq_false, dite_eq_ite]



theorem kl_poly_unique (C : CoxeterGroupData)
    (Q : C.W → C.W → Polynomial ℤ)
    (hQ_zero : ∀ y w, ¬ C.bruhatLE y w → Q y w = 0)
    (hQ_diag : ∀ w, Q w w = 1)
    (hQ_deg : ∀ y w, C.bruhatLE y w → y ≠ w →
      (Q y w).natDegree ≤ (C.length w - C.length y - 1) / 2)
    (hQ_recursion : ∀ y w, C.bruhatLE y w → y ≠ w →
      Q y w = mkBoundedPoly ((C.length w - C.length y - 1) / 2)
        (self_dual_coeffs C y w ((C.length w - C.length y - 1) / 2)
          (fun z => if C.bruhatLE y z ∧ z ≠ y ∧ C.bruhatLE z w then Q z w else 0)))
    (y w : C.W) :
    Q y w = KazhdanLusztigPoly C y w := by


  suffices key : ∀ (n : ℕ) (y' w' : C.W),
      C.length w' - C.length y' = n →
      Q y' w' = KazhdanLusztigPoly C y' w' from
    key (C.length w - C.length y) y w rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro y' w' hdiff
    by_cases hle : C.bruhatLE y' w'
    ·
      by_cases heq : y' = w'
      ·
        subst heq
        rw [hQ_diag, kl_poly_diag]
      ·
        have hlen_lt : C.length y' < C.length w' :=
          C.bruhat_length_strict y' w' hle heq

        have ih_applied : ∀ z : C.W, C.length y' < C.length z →
            C.bruhatLE z w' → Q z w' = KazhdanLusztigPoly C z w' := by
          intro z hz_gt hz_le
          apply ih (C.length w' - C.length z)
          · omega
          · rfl


        have hQ_rec := hQ_recursion y' w' hle heq

        have rec_eq : (fun z => if C.bruhatLE y' z ∧ z ≠ y' ∧ C.bruhatLE z w'
            then Q z w' else 0) =
            (fun z => if C.bruhatLE y' z ∧ z ≠ y' ∧ C.bruhatLE z w'
            then KazhdanLusztigPoly C z w' else 0) := by
          funext z
          split_ifs with h
          · exact ih_applied z
              (C.bruhat_length_strict y' z h.1 (Ne.symm h.2.1)) h.2.2
          · rfl
        rw [rec_eq] at hQ_rec

        rw [hQ_rec, klp_unfold C y' w' hle heq]
    ·
      rw [hQ_zero y' w' hle, kl_poly_zero_unless_bruhat_le C y' w' hle]

end
