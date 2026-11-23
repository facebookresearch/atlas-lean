/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable section

open scoped nonZeroDivisors

namespace LinearEquivDivisors


/-- The group of Weil divisors on `Y` as finitely supported functions `Y → ℤ`. -/
abbrev WeilDivisorGroup (Y : Type*) := Y →₀ ℤ

/-- A Weil divisor `D` is effective iff all of its coefficients are nonnegative. -/
def WeilDivisor.IsEffective {Y : Type*} (D : WeilDivisorGroup Y) : Prop :=
  ∀ y : Y, 0 ≤ D y

/-- Two Cartier divisors (nonzero ideals of a Dedekind domain) are linearly
equivalent iff they represent the same element of the class group. -/
def CartierDivisor.LinearlyEquivalent (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (I J : (Ideal A)⁰) : Prop :=
  ClassGroup.mk0 I = ClassGroup.mk0 J


variable {Y : Type*}

/-- The subgroup of principal Weil divisors inside the full Weil divisor group. -/
abbrev PrincipalDivisors (Y : Type*) := AddSubgroup (WeilDivisorGroup Y)

/-- Linear equivalence of Weil divisors modulo a chosen subgroup `P` of principal
divisors: `D₁ ~ D₂` iff `D₁ - D₂ ∈ P` (Def 32, Lec 16). -/
def WeilLinearlyEquivalent (P : PrincipalDivisors Y) (D₁ D₂ : WeilDivisorGroup Y) :
    Prop :=
  D₁ - D₂ ∈ P


/-- Linear equivalence of Weil divisors is an equivalence relation. -/
theorem weilLinearlyEquivalent_equivalence (P : PrincipalDivisors Y) :
    Equivalence (WeilLinearlyEquivalent P) where
  refl D := by
    show D - D ∈ P
    simp [P.zero_mem]
  symm {a b} h := by
    show b - a ∈ P
    have : b - a = -(a - b) := by abel
    rw [this]
    exact P.neg_mem h
  trans {a b c} h1 h2 := by
    show a - c ∈ P
    have : a - c = (a - b) + (b - c) := by abel
    rw [this]
    exact P.add_mem h1 h2

/-- Linear equivalence of Weil divisors is reflexive. -/
theorem WeilLinearlyEquivalent.refl (P : PrincipalDivisors Y)
    (D : WeilDivisorGroup Y) :
    WeilLinearlyEquivalent P D D :=
  (weilLinearlyEquivalent_equivalence P).refl D

/-- Linear equivalence of Weil divisors is symmetric. -/
theorem WeilLinearlyEquivalent.symm (P : PrincipalDivisors Y)
    {D₁ D₂ : WeilDivisorGroup Y} (h : WeilLinearlyEquivalent P D₁ D₂) :
    WeilLinearlyEquivalent P D₂ D₁ :=
  (weilLinearlyEquivalent_equivalence P).symm h

/-- Linear equivalence of Weil divisors is transitive. -/
theorem WeilLinearlyEquivalent.trans (P : PrincipalDivisors Y)
    {D₁ D₂ D₃ : WeilDivisorGroup Y}
    (h₁ : WeilLinearlyEquivalent P D₁ D₂) (h₂ : WeilLinearlyEquivalent P D₂ D₃) :
    WeilLinearlyEquivalent P D₁ D₃ :=
  (weilLinearlyEquivalent_equivalence P).trans h₁ h₂

/-- The setoid on Weil divisors given by linear equivalence relative to `P`. -/
def weilLinearEquivSetoid (P : PrincipalDivisors Y) :
    Setoid (WeilDivisorGroup Y) :=
  ⟨WeilLinearlyEquivalent P, weilLinearlyEquivalent_equivalence P⟩


/-- The degree of a Weil divisor is the sum of its coefficients. -/
def WeilDivisor.degree (D : WeilDivisorGroup Y) : ℤ :=
  D.sum (fun _ n => n)

/-- The zero divisor has degree zero. -/
theorem WeilDivisor.degree_zero :
    WeilDivisor.degree (0 : WeilDivisorGroup Y) = 0 := by
  simp [WeilDivisor.degree, Finsupp.sum_zero_index]

/-- Degree is additive on sums of Weil divisors. -/
theorem WeilDivisor.degree_add [DecidableEq Y] (D₁ D₂ : WeilDivisorGroup Y) :
    WeilDivisor.degree (D₁ + D₂) = WeilDivisor.degree D₁ + WeilDivisor.degree D₂ := by
  simp only [WeilDivisor.degree]
  rw [Finsupp.sum_add_index (by simp) (by intros; ring)]

/-- Negating a Weil divisor negates its degree. -/
theorem WeilDivisor.degree_neg (D : WeilDivisorGroup Y) :
    WeilDivisor.degree (-D) = -WeilDivisor.degree D := by
  simp only [WeilDivisor.degree]
  rw [Finsupp.sum_neg_index (by simp)]
  simp [Finsupp.sum, Finset.sum_neg_distrib]

/-- Degree is additive on differences of Weil divisors. -/
theorem WeilDivisor.degree_sub [DecidableEq Y] (D₁ D₂ : WeilDivisorGroup Y) :
    WeilDivisor.degree (D₁ - D₂) = WeilDivisor.degree D₁ - WeilDivisor.degree D₂ := by
  rw [sub_eq_add_neg, degree_add, degree_neg, sub_eq_add_neg]

variable [DecidableEq Y] in
/-- If every divisor in the principal subgroup `P` has degree zero, then linearly
equivalent Weil divisors have equal degree. -/
theorem WeilDivisor.degree_eq_of_linearlyEquiv {P : PrincipalDivisors Y}
    (hP : ∀ D ∈ P, WeilDivisor.degree D = 0)
    {D₁ D₂ : WeilDivisorGroup Y} (h : WeilLinearlyEquivalent P D₁ D₂) :
    WeilDivisor.degree D₁ = WeilDivisor.degree D₂ := by
  have := hP _ h
  rw [degree_sub] at this
  omega


/-- The complete linear system `|D|`: all effective Weil divisors linearly
equivalent to `D`. -/
def completeLinearSystem (P : PrincipalDivisors Y) (D : WeilDivisorGroup Y) :
    Set (WeilDivisorGroup Y) :=
  {D' | WeilDivisor.IsEffective D' ∧ WeilLinearlyEquivalent P D' D}

/-- Every member of `|D|` is effective. -/
theorem mem_completeLinearSystem_isEffective (P : PrincipalDivisors Y)
    {D D' : WeilDivisorGroup Y} (h : D' ∈ completeLinearSystem P D) :
    WeilDivisor.IsEffective D' :=
  h.1

/-- Every member of `|D|` is linearly equivalent to `D`. -/
theorem mem_completeLinearSystem_equiv (P : PrincipalDivisors Y)
    {D D' : WeilDivisorGroup Y} (h : D' ∈ completeLinearSystem P D) :
    WeilLinearlyEquivalent P D' D :=
  h.2

/-- An effective Weil divisor belongs to its own complete linear system. -/
theorem self_mem_completeLinearSystem (P : PrincipalDivisors Y)
    {D : WeilDivisorGroup Y} (hD : WeilDivisor.IsEffective D) :
    D ∈ completeLinearSystem P D :=
  ⟨hD, WeilLinearlyEquivalent.refl P D⟩

/-- With the full principal subgroup, the complete linear system is the set of all
effective divisors. -/
theorem completeLinearSystem_top_eq (D : WeilDivisorGroup Y) :
    completeLinearSystem ⊤ D = {D' | WeilDivisor.IsEffective D'} := by
  ext D'
  simp [completeLinearSystem, WeilLinearlyEquivalent]

/-- With trivial principal subgroup, the complete linear system reduces to `{D}`
intersected with the effective cone. -/
theorem completeLinearSystem_bot_eq (D : WeilDivisorGroup Y) :
    completeLinearSystem ⊥ D =
    {D' | WeilDivisor.IsEffective D' ∧ D' = D} := by
  ext D'
  simp [completeLinearSystem, WeilLinearlyEquivalent, AddSubgroup.mem_bot, sub_eq_zero]


/-- Linear equivalence of Cartier divisors on a Dedekind domain is an equivalence
relation. -/
theorem cartierLinearlyEquivalent_equivalence (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] :
    Equivalence (fun I J : (Ideal A)⁰ =>
      CartierDivisor.LinearlyEquivalent A I J) where
  refl _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂


/-- A nonzero ideal is principal iff its image in the class group is trivial. -/
theorem cartierDivisor_principal_iff_trivialClass (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] (I : Ideal A) (hI : I ∈ (Ideal A)⁰) :
    ClassGroup.mk0 ⟨I, hI⟩ = 1 ↔ Submodule.IsPrincipal I :=
  ClassGroup.mk0_eq_one_iff hI


/-- Dimension of a complete linear system, defined as `dim_k V - 1` where `V`
is the global sections module. -/
def completeLinearSystemDim (k : Type*) [Field k] (V : Type*)
    [AddCommGroup V] [Module k V] [Module.Finite k V] : ℤ :=
  (Module.finrank k V : ℤ) - 1

/-- Definitional unfolding of `completeLinearSystemDim`. -/
theorem completeLinearSystemDim_eq (k : Type*) [Field k] (V : Type*)
    [AddCommGroup V] [Module k V] [Module.Finite k V] :
    completeLinearSystemDim k V = (Module.finrank k V : ℤ) - 1 :=
  rfl

/-- If `V` has positive `k`-dimension, the linear system dimension is nonneg. -/
theorem completeLinearSystemDim_nonneg (k : Type*) [Field k] (V : Type*)
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    (hV : 0 < Module.finrank k V) :
    0 ≤ completeLinearSystemDim k V := by
  simp [completeLinearSystemDim]
  omega

/-- Nontriviality of `V` yields a nonempty projectivization, so a nonempty
linear system. -/
theorem completeLinearSystem_nonempty_of_nontrivial (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [Nontrivial V] :
    Nonempty (Projectivization k V) :=
  inferInstance


/-- The zero divisor is effective. -/
theorem WeilDivisor.IsEffective_zero :
    WeilDivisor.IsEffective (0 : WeilDivisorGroup Y) :=
  fun _ => le_refl 0

/-- The sum of two effective Weil divisors is effective. -/
theorem WeilDivisor.IsEffective_add {D₁ D₂ : WeilDivisorGroup Y}
    (h₁ : WeilDivisor.IsEffective D₁) (h₂ : WeilDivisor.IsEffective D₂) :
    WeilDivisor.IsEffective (D₁ + D₂) :=
  fun y => by simp [Finsupp.add_apply]; exact add_nonneg (h₁ y) (h₂ y)

end LinearEquivDivisors

end
