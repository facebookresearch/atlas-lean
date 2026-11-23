/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.ClassGroup
import Atlas.EllipticCurves.code.ComplexMultiplication
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic

namespace FieldNormTrace

section General

/-- The field norm `K → k` of a `k`-algebra `K`, packaged as a monoid homomorphism. -/
noncomputable abbrev fieldNorm (k : Type*) {K : Type*}
    [CommRing k] [Ring K] [Algebra k K] : K →* k :=
  Algebra.norm k

/-- The field trace `K → k` of a `k`-algebra `K`, packaged as a `k`-linear map. -/
noncomputable abbrev fieldTrace (k : Type*) (K : Type*)
    [CommRing k] [CommRing K] [Algebra k K] : K →ₗ[k] k :=
  Algebra.trace k K

end General

section Quadratic

variable {D : ℤ}

/-- The norm form on `ℤ√D`: `N(α) = α.re² - D · α.im²`. -/
theorem norm_eq_sq (α : ℤ√D) : α.norm = α.re ^ 2 - D * α.im ^ 2 := by
  simp only [Zsqrtd.norm_def, sq]; ring

/-- The norm of `α ∈ ℤ√D`, embedded back into `ℤ√D`, equals `α · star α`. -/
theorem norm_eq_mul_conj (α : ℤ√D) : (α.norm : ℤ√D) = α * star α :=
  Zsqrtd.norm_eq_mul_conj α

/-- The trace form on `ℤ√D`: `α + star α = 2 · α.re` (as an element of `ℤ√D`). -/
theorem trace_eq (α : ℤ√D) : α + star α = ↑(2 * α.re) := by
  ext <;> simp [Zsqrtd.re_star, Zsqrtd.im_star, two_mul]

/-- The real part of `α + star α` equals `2 · α.re`. -/
theorem trace_re (α : ℤ√D) : (α + star α).re = 2 * α.re := by
  simp [Zsqrtd.re_add, Zsqrtd.re_star, two_mul]

/-- The imaginary part of `α + star α` vanishes. -/
theorem trace_im (α : ℤ√D) : (α + star α).im = 0 := by
  simp [Zsqrtd.im_add, Zsqrtd.im_star]

/-- The conjugate `star α` equals `2 · α.re - α`. -/
theorem conj_eq_trace_sub (α : ℤ√D) : star α = ↑(2 * α.re) - α := by
  ext <;> simp [Zsqrtd.re_star, Zsqrtd.im_star, two_mul]

/-- The real part of `α · star α` equals the norm `α.re² - D · α.im²`. -/
theorem mul_star_re (α : ℤ√D) :
    (α * star α).re = α.re ^ 2 - D * α.im ^ 2 := by
  simp [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star, sq]; ring

/-- The imaginary part of `α · star α` vanishes. -/
theorem mul_star_im (α : ℤ√D) : (α * star α).im = 0 := by
  simp [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]; ring

/-- Multiplicativity of the norm on `ℤ√D`: `N(αβ) = N(α) · N(β)`. -/
theorem norm_mul (α β : ℤ√D) : (α * β).norm = α.norm * β.norm :=
  Zsqrtd.norm_mul α β

/-- The norm is invariant under conjugation: `N(star α) = N(α)`. -/
theorem norm_conj (α : ℤ√D) : (star α).norm = α.norm :=
  Zsqrtd.norm_conj α

/-- For `D ≤ 0` (imaginary quadratic case), the norm on `ℤ√D` is nonnegative. -/
theorem norm_nonneg (hD : D ≤ 0) (α : ℤ√D) : 0 ≤ α.norm :=
  Zsqrtd.norm_nonneg hD α

end Quadratic

end FieldNormTrace

namespace QuadraticOrder

/-- The discriminant `t² - 4n` of a monic quadratic `x² - t x + n`. -/
def disc (t n : ℤ) : ℤ := t ^ 2 - 4 * n

/-- Defining equation for `disc`: `disc t n = t² - 4n`. -/
@[simp]
theorem disc_def (t n : ℤ) : disc t n = t ^ 2 - 4 * n := rfl

section Zsqrtd

variable {d : ℤ} (τ : ℤ√d)

/-- The integer trace of `τ ∈ ℤ√d`, defined as `2 · τ.re`. -/
def traceZ : ℤ := 2 * τ.re

/-- Defining equation for `traceZ`. -/
@[simp]
theorem traceZ_eq : traceZ τ = 2 * τ.re := rfl

/-- The discriminant of `τ ∈ ℤ√d`, given by `disc (traceZ τ) (N τ)`. -/
def discZsqrtd : ℤ := disc (traceZ τ) (Zsqrtd.norm τ)

/-- Computation: the discriminant of `τ ∈ ℤ√d` equals `4 d · τ.im²`. -/
@[simp]
theorem discZsqrtd_eq : discZsqrtd τ = 4 * d * τ.im ^ 2 := by
  simp only [discZsqrtd, disc, traceZ, Zsqrtd.norm_def]
  ring

/-- The discriminant of `τ` can also be expressed as `Re((τ - star τ)²)`. -/
theorem discZsqrtd_eq_sq_sub_conj_re :
    discZsqrtd τ = ((τ - star τ) * (τ - star τ)).re := by
  simp only [discZsqrtd, disc, traceZ, Zsqrtd.norm_def,
    Zsqrtd.re_star, Zsqrtd.im_star, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_mul]
  ring

/-- The imaginary part of `(τ - star τ)²` vanishes. -/
theorem sq_sub_conj_im_eq_zero :
    ((τ - star τ) * (τ - star τ)).im = 0 := by
  simp only [Zsqrtd.re_star, Zsqrtd.im_star, Zsqrtd.im_sub, Zsqrtd.re_sub, Zsqrtd.im_mul]
  ring

/-- The discriminant of `τ` equals `(traceZ τ)² - 4 · N(τ)`, exhibiting it as the
discriminant of the minimal polynomial. -/
theorem discZsqrtd_eq_trace_sq_sub_four_norm :
    discZsqrtd τ = (traceZ τ) ^ 2 - 4 * (Zsqrtd.norm τ) := by
  simp only [discZsqrtd, disc]

/-- The element `√d ∈ ℤ√d` has discriminant `4d`. -/
theorem discZsqrtd_sqrtd : discZsqrtd (⟨0, 1⟩ : ℤ√d) = 4 * d := by
  simp [discZsqrtd_eq]

end Zsqrtd

end QuadraticOrder

namespace ImaginaryQuadraticDiscriminant

/-- `D` is an imaginary quadratic discriminant if `D < 0` and `D ≡ 0` or `1 (mod 4)`. -/
def IsImaginaryQuadraticDiscriminant (D : ℤ) : Prop :=
  D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1)

/-- `D` is a fundamental imaginary quadratic discriminant if it is an imaginary quadratic
discriminant and is not of the form `u² · D'` for `u > 1` and another imaginary quadratic
discriminant `D'`. -/
def IsFundamentalImaginaryQuadraticDiscriminant (D : ℤ) : Prop :=
  IsImaginaryQuadraticDiscriminant D ∧
    ∀ u D' : ℤ, u > 1 → IsImaginaryQuadraticDiscriminant D' → D ≠ u ^ 2 * D'

/-- A decomposition `D = u² · D_K` of an imaginary quadratic discriminant `D` into the
conductor `u ≥ 1` and the fundamental discriminant `D_K` of the maximal order. -/
structure ImaginaryQuadraticDiscriminantDecomposition (D : ℤ) where
  u : ℤ
  D_K : ℤ
  hu : u ≥ 1
  hD_K : IsFundamentalImaginaryQuadraticDiscriminant D_K
  hD : D = u ^ 2 * D_K

/-- Every imaginary quadratic discriminant `D` admits a decomposition `D = u² · D_K`
where `D_K` is fundamental and `u ≥ 1`. -/
theorem discriminant_decomposition_exists
    (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    ∃ D_K : ℤ, ∃ u : ℤ, u ≥ 1 ∧ IsFundamentalImaginaryQuadraticDiscriminant D_K ∧ D = u ^ 2 * D_K := by
  suffices h : ∀ n : ℕ, ∀ D : ℤ, (-D).toNat = n → IsImaginaryQuadraticDiscriminant D →
    ∃ D_K : ℤ, ∃ u : ℤ, u ≥ 1 ∧ IsFundamentalImaginaryQuadraticDiscriminant D_K ∧
      D = u ^ 2 * D_K from
    h _ D rfl hD
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro D hn hD
    by_cases hfund : IsFundamentalImaginaryQuadraticDiscriminant D
    · exact ⟨D, 1, le_refl 1, hfund, by ring⟩
    · unfold IsFundamentalImaginaryQuadraticDiscriminant at hfund
      push Not at hfund
      obtain ⟨u, D', hu, hD', heq⟩ := hfund hD
      have hD'neg : D' < 0 := hD'.1
      have hDneg : D < 0 := hD.1
      have hlt : (-D').toNat < n := by
        rw [← hn]
        have hu2ge : u ^ 2 ≥ 4 := by nlinarith
        have key : -D' < -D := by nlinarith
        omega
      obtain ⟨D_K, v, hv, hfundK, heq'⟩ := ih _ hlt D' rfl hD'
      refine ⟨D_K, u * v, ?_, hfundK, ?_⟩
      · nlinarith
      · rw [heq, heq']; ring


end ImaginaryQuadraticDiscriminant

open nonZeroDivisors

/-- Convenient abbreviation `FractionalOIdeal R K` for the type of fractional `R`-ideals
in the fraction field `K`. -/
abbrev FractionalOIdeal (R : Type*) [CommRing R] [IsDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  FractionalIdeal R⁰ K

namespace FractionalOIdeal

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]

open FractionalIdeal

set_option linter.unusedSectionVars false in
/-- Multiplicativity formula for fractional ideals written in the form `(l) · a` where `l`
is a scalar and `a` an integral ideal: `((l)·a) · ((l')·a') = (l·l') · (a·a')`. -/
theorem mul_eq (l l' : K) (a a' : Ideal R) :
    (spanSingleton R⁰ l * (a : FractionalIdeal R⁰ K)) *
    (spanSingleton R⁰ l' * (a' : FractionalIdeal R⁰ K)) =
    spanSingleton R⁰ (l * l') * ((a * a' : Ideal R) : FractionalIdeal R⁰ K) := by
  rw [coeIdeal_mul, ← spanSingleton_mul_spanSingleton]
  ring

end FractionalOIdeal

namespace NormTrace

variable {𝒪 : Type*} [CommRing 𝒪]

/-- The ideal norm `N(𝔞) := |𝒪/𝔞|`, defined as the cardinality of the quotient ring. -/
noncomputable def idealNorm (𝔞 : Ideal 𝒪) : ℕ := Submodule.cardQuot 𝔞

/-- Defining property of `idealNorm`: it equals the cardinality of `𝒪 / 𝔞`. -/
theorem idealNorm_eq_card_quotient (𝔞 : Ideal 𝒪) :
    idealNorm 𝔞 = Nat.card (𝒪 ⧸ 𝔞) :=
  Submodule.cardQuot_apply 𝔞

/-- The norm of the unit ideal is 1. -/
theorem idealNorm_top : idealNorm (⊤ : Ideal 𝒪) = 1 :=
  Submodule.cardQuot_top 𝒪 𝒪

/-- The norm of the zero ideal in an infinite ring is 0. -/
theorem idealNorm_bot [Infinite 𝒪] : idealNorm (⊥ : Ideal 𝒪) = 0 :=
  Submodule.cardQuot_bot 𝒪 𝒪

/-- For a free, finite `ℤ`-module domain `𝒪`, every nonzero ideal has positive (and hence
finite, nonzero) norm. -/
theorem idealNorm_pos {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [Module.Free ℤ 𝒪] [Module.Finite ℤ 𝒪] (𝔞 : Ideal 𝒪) (h : 𝔞 ≠ ⊥) :
    0 < idealNorm 𝔞 := by
  rw [idealNorm, Submodule.cardQuot_apply, Nat.pos_iff_ne_zero, Nat.card_ne_zero]
  exact ⟨⟨Ideal.Quotient.mk 𝔞 0⟩, Ideal.finiteQuotientOfFreeOfNeBot 𝔞 h⟩

/-- For a Dedekind domain `𝒪` that is free as a `ℤ`-module, the `Ideal.absNorm` agrees
with the cardinality-based `idealNorm` defined here. -/
theorem idealNorm_eq_absNorm {𝒪 : Type*} [CommRing 𝒪] [Nontrivial 𝒪]
    [IsDedekindDomain 𝒪] [Module.Free ℤ 𝒪] (𝔞 : Ideal 𝒪) :
    Ideal.absNorm 𝔞 = idealNorm 𝔞 :=
  Ideal.absNorm_apply 𝔞

end NormTrace

namespace PrincipalIdealNorm

open NormTrace

variable {𝒪 : Type*} [CommRing 𝒪] [IsDedekindDomain 𝒪]
    [Module.Free ℤ 𝒪] [Module.Finite ℤ 𝒪]

/-- For a principal ideal `(α)` in a Dedekind domain, the ideal norm equals `|N(α)|`,
as natural numbers. -/
theorem idealNorm_span_singleton_eq_natAbs_norm (α : 𝒪) :
    idealNorm (Ideal.span {α}) = (Algebra.norm ℤ α).natAbs := by
  rw [idealNorm, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]

/-- Integer version: `(N (α)) = |N_{𝒪/ℤ}(α)|` for principal ideals. -/
theorem idealNorm_span_singleton_eq_abs_norm (α : 𝒪) :
    (idealNorm (Ideal.span {α}) : ℤ) = |Algebra.norm ℤ α| := by
  rw [idealNorm_span_singleton_eq_natAbs_norm]
  simp

end PrincipalIdealNorm

namespace PrincipalIdealNorm

open NormTrace NumberField

open scoped NumberField

/-- Specialised version for the ring of integers of a number field `K`: `N((α)) =
|N_{K/ℚ}(α)|`. -/
theorem idealNorm_principal_ringOfIntegers (K : Type*) [Field K] [NumberField K]
    (α : 𝓞 K) :
    Ideal.absNorm (Ideal.span {α}) = (Algebra.norm ℤ α).natAbs :=
  Ideal.absNorm_span_singleton α

end PrincipalIdealNorm

namespace IdealNormMultiplicativity

open NormTrace

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [Module.Free ℤ 𝒪] [Module.Finite ℤ 𝒪]

/-- Membership lemma: any element of `(α) · 𝔞` is of the form `α · w` for some `w ∈ 𝔞`. -/
lemma mem_span_singleton_mul {α : 𝒪} {𝔞 : Ideal 𝒪} {z : 𝒪}
    (hz : z ∈ Ideal.span {α} * 𝔞) : ∃ w ∈ 𝔞, z = α * w := by
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro a ha b hb
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨r, rfl⟩ := ha
    exact ⟨r * b, 𝔞.mul_mem_left r hb, by ring⟩
  · rintro _ _ ⟨wx, hwx_mem, rfl⟩ ⟨wy, hwy_mem, rfl⟩
    exact ⟨wx + wy, 𝔞.add_mem hwx_mem hwy_mem, by ring⟩

/-- Multiplicativity of the ideal norm against a principal ideal:
`N((α) · 𝔞) = N((α)) · N(𝔞)`. -/
theorem idealNorm_mul_principal (α : 𝒪) (𝔞 : Ideal 𝒪) :
    idealNorm (Ideal.span {α} * 𝔞) = idealNorm (Ideal.span {α}) * idealNorm 𝔞 := by
  by_cases hα : α = 0
  · subst hα
    haveI : Infinite 𝒪 := Module.Free.infinite ℤ 𝒪
    have h0 : Ideal.span {(0 : 𝒪)} = ⊥ := Ideal.span_singleton_eq_bot.mpr rfl
    rw [h0, Ideal.bot_mul, idealNorm_bot, zero_mul]

  have hle : (Ideal.span {α} * 𝔞 : Ideal 𝒪) ≤ Ideal.span {α} :=
    (Ideal.mul_mono_right le_top).trans (Ideal.mul_top _).le
  have htower := Submodule.card_quotient_mul_card_quotient
    (Ideal.span {α} : Submodule 𝒪 𝒪) (↑(Ideal.span {α} * 𝔞)) hle
  simp only [idealNorm, Submodule.cardQuot_apply]
  rw [← htower, mul_comm]
  congr 1

  set P := Submodule.map (↑(Ideal.span {α} * 𝔞) : Submodule 𝒪 𝒪).mkQ
    (↑(Ideal.span {α}) : Submodule 𝒪 𝒪)
  have hmem : ∀ x : 𝒪, α * x ∈ (Ideal.span {α} : Submodule 𝒪 𝒪) :=
    fun x => Ideal.mul_mem_right x _ (Ideal.mem_span_singleton_self α)
  symm; apply Nat.card_congr
  let f : 𝒪 → P := fun x => ⟨Submodule.Quotient.mk (α * x), ⟨α * x, hmem x, rfl⟩⟩
  have hf : ∀ a b : 𝒪, a - b ∈ (𝔞 : Submodule 𝒪 𝒪) → f a = f b := by
    intro a b hab
    apply Subtype.ext
    show Submodule.Quotient.mk (α * a) = Submodule.Quotient.mk (α * b)
    rw [Submodule.Quotient.eq]
    show α * a - α * b ∈ (↑(Ideal.span {α} * 𝔞) : Submodule 𝒪 𝒪)
    rw [show α * a - α * b = α * (a - b) from by ring]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self α) hab
  let F : 𝒪 ⧸ (𝔞 : Submodule 𝒪 𝒪) → P :=
    Quotient.lift f (fun a b h => hf a b ((Submodule.quotientRel_def (p := 𝔞)).mp h))
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  ·
    intro a b hab
    induction a using Quotient.inductionOn with | _ a => ?_
    induction b using Quotient.inductionOn with | _ b => ?_
    show Quotient.mk _ a = Quotient.mk _ b
    rw [Quotient.eq]
    show (𝔞 : Submodule 𝒪 𝒪).quotientRel a b
    rw [Submodule.quotientRel_def]

    change f a = f b at hab
    have h2 := congr_arg Subtype.val hab
    simp only [f] at h2
    rw [Submodule.Quotient.eq] at h2
    change α * a - α * b ∈ (Ideal.span {α} * 𝔞 : Ideal 𝒪) at h2
    rw [show α * a - α * b = α * (a - b) from by ring] at h2
    obtain ⟨w, hw_mem, hw_eq⟩ := mem_span_singleton_mul h2
    exact (mul_left_cancel₀ hα hw_eq).symm ▸ hw_mem
  ·
    rintro ⟨q, hq⟩
    obtain ⟨y, hy_mem, hy_eq⟩ := hq

    have hy_mem' : y ∈ Ideal.span {α} := hy_mem
    rw [Ideal.mem_span_singleton'] at hy_mem'
    obtain ⟨c, rfl⟩ := hy_mem'
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    show f c = ⟨q, _⟩
    apply Subtype.ext
    show Submodule.Quotient.mk (α * c) = q
    rw [show α * c = c * α from mul_comm α c]
    exact hy_eq

/-- Refined version in the Dedekind case: `N((α) · 𝔞) = |N(α)| · N(𝔞)`. -/
theorem idealNorm_smul_eq_natAbs_mul [IsDedekindDomain 𝒪] (α : 𝒪) (𝔞 : Ideal 𝒪) :
    idealNorm (Ideal.span {α} * 𝔞) = (Algebra.norm ℤ α).natAbs * idealNorm 𝔞 := by
  rw [idealNorm_mul_principal]
  congr 1
  simp only [idealNorm, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]

end IdealNormMultiplicativity

open scoped Pointwise

namespace FractionalIdealNorm

variable {𝒪 : Type*} [CommRing 𝒪] [IsDedekindDomain 𝒪] [Module.Free ℤ 𝒪] [Module.Finite ℤ 𝒪]
variable {K : Type*} [CommRing K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

open nonZeroDivisors

/-- The norm of a fractional ideal `𝔟 = (1/d) · 𝔟.num`: `N(𝔟) = N(𝔟.num) / |N(𝔟.den)|`,
as a rational number. -/
noncomputable def fractionalIdealNorm (𝔟 : FractionalIdeal 𝒪⁰ K) : ℚ :=
  (Ideal.absNorm 𝔟.num : ℚ) / |Algebra.norm ℤ (𝔟.den : 𝒪)|

/-- The fractional ideal norm defined here agrees with Mathlib's
`FractionalIdeal.absNorm`. -/
theorem fractionalIdealNorm_eq_absNorm (𝔟 : FractionalIdeal 𝒪⁰ K) :
    fractionalIdealNorm 𝔟 = FractionalIdeal.absNorm 𝔟 :=
  (FractionalIdeal.absNorm_eq 𝔟).symm

/-- Definitional unfolding of `fractionalIdealNorm`. -/
theorem fractionalIdealNorm_eq (𝔟 : FractionalIdeal 𝒪⁰ K) :
    fractionalIdealNorm 𝔟 =
      (Ideal.absNorm 𝔟.num : ℚ) / |Algebra.norm ℤ (𝔟.den : 𝒪)| :=
  rfl

end FractionalIdealNorm

open Module

noncomputable section

/-- For any `ℤ`-submodule `N` of `M`, the cardinality of `M/N` (as a natural number) times
`x` lies in `N`, for every `x ∈ M`. -/
lemma nsmul_mem_of_card_quotient {M : Type*} [AddCommGroup M] [Module ℤ M]
    (N : Submodule ℤ M) (x : M) :
    (Nat.card (M ⧸ N)) • x ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero]
  show N.mkQ ((Nat.card (M ⧸ N)) • x) = 0
  rw [map_nsmul]
  exact card_nsmul_eq_zero'

/-- Integer-scalar version of `nsmul_mem_of_card_quotient`. -/
lemma zsmul_mem_of_card_quotient {M : Type*} [AddCommGroup M] [Module ℤ M]
    (N : Submodule ℤ M) (x : M) :
    (Nat.card (M ⧸ N) : ℤ) • x ∈ N := by
  rw [natCast_zsmul]
  exact nsmul_mem_of_card_quotient N x

/-- For `n : ℤ`, the image `n · (Fin 2 → ℤ)` under scalar multiplication equals the
product of singleton spans `Π i, ⟨n⟩`. -/
lemma nsmul_top_eq_pi (n : ℤ) :
    Submodule.map (n • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ))) ⊤ =
    Submodule.pi Set.univ (fun _ : Fin 2 => Submodule.span ℤ {n}) := by
  ext x
  simp only [Submodule.mem_map, Submodule.mem_top, true_and, LinearMap.smul_apply,
    LinearMap.id_apply, Submodule.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact Submodule.mem_span_singleton.mpr ⟨y i, mul_comm (y i) n⟩
  · intro h
    choose c hc using fun i => Submodule.mem_span_singleton.mp (h i)
    refine ⟨c, funext fun i => ?_⟩
    show n * c i = x i
    rw [mul_comm]; exact hc i

/-- The cardinality of `ℤ / ⟨n⟩` equals `n` (for a natural number `n`). -/
lemma nat_card_int_quotient_span (n : ℕ) :
    Nat.card (ℤ ⧸ Submodule.span ℤ {(n : ℤ)}) = n := by
  change Nat.card (ℤ ⧸ Ideal.span {(n : ℤ)}) = n
  rw [Nat.card_congr (Int.quotientSpanEquivZMod (n : ℤ)).toEquiv]
  simp [Int.natAbs_natCast, Nat.card_zmod]

/-- The cardinality of `(Fin 2 → ℤ) / n·(Fin 2 → ℤ)` equals `n²`. -/
lemma nat_card_quotient_nsmul (n : ℕ) :
    Nat.card ((Fin 2 → ℤ) ⧸
      (Submodule.map ((n : ℤ) • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] _)) ⊤)) = n ^ 2 := by
  rw [nsmul_top_eq_pi]
  rw [Nat.card_congr (Submodule.quotientPi _).toEquiv, Nat.card_pi]
  simp only [nat_card_int_quotient_span, Finset.prod_const, Finset.card_fin]

/-- For a sublattice `N` of `(Fin 2 → ℤ)` of index `n`, the sublattice `n·(Fin 2 → ℤ)` is
contained in `N`. -/
lemma nsmul_le_of_card_quotient (N : Submodule ℤ (Fin 2 → ℤ)) (n : ℕ)
    (hindex : Nat.card ((Fin 2 → ℤ) ⧸ N) = n) :
    Submodule.map ((n : ℤ) • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] _)) ⊤ ≤ N := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hx
  show (n : ℤ) • y ∈ N
  rw [← hindex]
  exact zsmul_mem_of_card_quotient N y

/-- For a sublattice `N` of `(Fin 2 → ℤ)` of index `n > 0`, the image of `N` in
`(Fin 2 → ℤ) / n·(Fin 2 → ℤ)` also has cardinality `n`. -/
theorem sublattice_index_nsmul (N : Submodule ℤ (Fin 2 → ℤ)) (n : ℕ) (hn : 0 < n)
    (hindex : Nat.card ((Fin 2 → ℤ) ⧸ N) = n) :
    Nat.card ↥(Submodule.map
      (Submodule.map ((n : ℤ) • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] _)) ⊤).mkQ N) = n := by
  set nM := Submodule.map ((n : ℤ) • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] _)) ⊤
  have hle : nM ≤ N := nsmul_le_of_card_quotient N n hindex
  have htower := Submodule.card_quotient_mul_card_quotient N nM hle
  rw [hindex, nat_card_quotient_nsmul] at htower
  have hn' : n ≠ 0 := by omega
  have : Nat.card ↥(Submodule.map nM.mkQ N) * n = n * n := by rw [htower]; ring
  exact mul_right_cancel₀ hn' this

end

namespace ComplexLattice

open Pointwise

/-- The endomorphism ring of a complex lattice is invariant under homothety: if `L` and
`L'` are homothetic, then `End(L) = End(L')`. -/
theorem endomorphismRing_eq_of_homothetic {L L' : ComplexLattice}
    (h : IsHomothetic L L') : L'.endomorphismRing = L.endomorphismRing := by
  obtain ⟨c, hc, hcL⟩ := h
  ext α
  simp only [Subring.mem_mk, endomorphismRing]
  constructor
  ·
    intro hα z hz
    have hcz : c * z ∈ L'.lattice.toAddSubgroup := by
      show c • z ∈ (L'.lattice : Set ℂ)
      rw [hcL]
      exact Set.smul_mem_smul_set hz
    have hacv := hα (c * z) hcz
    rw [show α * (c * z) = c * (α * z) from by ring] at hacv
    change c • (α * z) ∈ (L'.lattice : Set ℂ) at hacv
    rw [hcL, Set.mem_smul_set_iff_inv_smul_mem₀ hc] at hacv
    simpa only [smul_eq_mul, inv_mul_cancel_left₀ hc] using hacv
  ·
    intro hα z hz
    have hz' : z ∈ (L'.lattice : Set ℂ) := hz
    rw [hcL, Set.mem_smul_set] at hz'
    obtain ⟨w, hw, rfl⟩ := hz'
    show α * (c • w) ∈ (L'.lattice : Set ℂ)
    rw [hcL]
    simp only [smul_eq_mul]
    rw [show α * (c * w) = c * (α * w) from by ring]
    exact Set.smul_mem_smul_set (hα w hw)

/-- Being a proper `𝒪`-ideal is preserved under homothety of lattices. -/
theorem IsProperIdeal.of_homothetic {𝒪 : Subring ℂ} {L L' : ComplexLattice}
    (hL : IsProperIdeal 𝒪 L) (hom : IsHomothetic L L') : IsProperIdeal 𝒪 L' := by
  unfold IsProperIdeal at *
  rw [endomorphismRing_eq_of_homothetic hom, hL]

/-- Equivalence: `L` is a proper `𝒪`-ideal iff its homothetic image `L'` is. -/
theorem isProperIdeal_iff_of_homothetic {𝒪 : Subring ℂ} {L L' : ComplexLattice}
    (hom : IsHomothetic L L') : IsProperIdeal 𝒪 L ↔ IsProperIdeal 𝒪 L' :=
  ⟨fun h => h.of_homothetic hom, fun h => h.of_homothetic hom.symm⟩

end ComplexLattice

namespace FractionalOIdeal

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]

open FractionalIdeal nonZeroDivisors

end FractionalOIdeal

namespace ImagQuadDiscriminant

open QuadraticOrder ImaginaryQuadraticDiscriminant

/-- An imaginary quadratic order, presented by a trace `t` and a norm `n` such that the
discriminant `t² - 4n` is negative and `≡ 0` or `1 (mod 4)`. -/
structure ImaginaryQuadraticOrder where
  t : ℤ
  n : ℤ
  hdisc_neg : t ^ 2 - 4 * n < 0
  hdisc_mod : (t ^ 2 - 4 * n) % 4 = 0 ∨ (t ^ 2 - 4 * n) % 4 = 1

/-- The discriminant `t² - 4n` of an imaginary quadratic order. -/
def ImaginaryQuadraticOrder.discriminant (𝒪 : ImaginaryQuadraticOrder) : ℤ :=
  𝒪.t ^ 2 - 4 * 𝒪.n

/-- Two imaginary quadratic orders agree (define the same order) when they have the same
discriminant and the same trace parity. -/
def ImaginaryQuadraticOrder.SameOrder (𝒪₁ 𝒪₂ : ImaginaryQuadraticOrder) : Prop :=
  𝒪₁.discriminant = 𝒪₂.discriminant ∧ 𝒪₁.t % 2 = 𝒪₂.t % 2

/-- Case split for `t² (mod 4)`: either `t` is even and `t² ≡ 0 (mod 4)`, or `t` is odd
and `t² ≡ 1 (mod 4)`. -/
lemma sq_mod_four_iff (t : ℤ) :
    (t % 2 = 0 ∧ t ^ 2 % 4 = 0) ∨ (t % 2 = 1 ∧ t ^ 2 % 4 = 1) := by
  rcases (show t % 2 = 0 ∨ t % 2 = 1 by omega) with h | h
  · left; exact ⟨h, by
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h; subst hk; ring_nf; omega⟩
  · right; refine ⟨h, ?_⟩
    have ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero (show (t - 1) % 2 = 0 by omega)
    have : t = 2 * k + 1 := by omega
    subst this; ring_nf; omega

/-- If `t₁² ≡ t₂² (mod 4)`, then `t₁` and `t₂` have the same parity. -/
lemma mod_two_eq_of_sq_mod_four_eq {t₁ t₂ : ℤ} (h : t₁ ^ 2 % 4 = t₂ ^ 2 % 4) :
    t₁ % 2 = t₂ % 2 := by
  rcases sq_mod_four_iff t₁ with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
  rcases sq_mod_four_iff t₂ with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;>
  omega

/-- If two trace-norm pairs `(t₁, n₁)` and `(t₂, n₂)` have the same discriminant, then
their traces have the same parity. -/
lemma trace_parity_eq_of_disc_eq {t₁ n₁ t₂ n₂ : ℤ}
    (heq : t₁ ^ 2 - 4 * n₁ = t₂ ^ 2 - 4 * n₂) :
    t₁ % 2 = t₂ % 2 :=
  mod_two_eq_of_sq_mod_four_eq (by omega)

/-- Existence: every imaginary quadratic discriminant `D` arises from some
`ImaginaryQuadraticOrder`. -/
theorem existence (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    ∃ 𝒪 : ImaginaryQuadraticOrder, 𝒪.discriminant = D := by
  obtain ⟨hlt, hmod⟩ := hD
  rcases hmod with h0 | h1
  ·
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
    exact ⟨⟨0, -k, by omega, Or.inl (by omega)⟩, by
      simp [ImaginaryQuadraticOrder.discriminant]; omega⟩
  ·
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero (show (1 - D) % 4 = 0 by omega)
    exact ⟨⟨1, k, by omega, Or.inr (by omega)⟩, by
      simp [ImaginaryQuadraticOrder.discriminant]; omega⟩

/-- Uniqueness: two `ImaginaryQuadraticOrder`s with the same discriminant satisfy
`SameOrder`. -/
theorem uniqueness (𝒪₁ 𝒪₂ : ImaginaryQuadraticOrder)
    (hD : 𝒪₁.discriminant = 𝒪₂.discriminant) :
    𝒪₁.SameOrder 𝒪₂ :=
  ⟨hD, trace_parity_eq_of_disc_eq (by
    simp only [ImaginaryQuadraticOrder.discriminant] at hD; exact hD)⟩

/-- Construct an `ImaginaryQuadraticOrder` of discriminant `D = u² · D_K` from the
decomposition `dec` into a conductor `u` and a fundamental discriminant `D_K`. -/
def orderFromDecomposition {D : ℤ}
    (dec : ImaginaryQuadraticDiscriminantDecomposition D) :
    ImaginaryQuadraticOrder where


  t := if dec.D_K % 4 = 0 then 0 else dec.u


  n := if dec.D_K % 4 = 0 then
    -(dec.u ^ 2 * (dec.D_K / 4))
  else
    -(dec.u ^ 2 * ((dec.D_K - 1) / 4))
  hdisc_neg := by
    have hu_sq_pos : dec.u ^ 2 ≥ 1 := by nlinarith [dec.hu]
    rcases dec.hD_K.1.2 with h0 | h1
    · simp only [h0, ↑reduceIte]
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
      have hk_neg : k < 0 := by nlinarith [dec.hD_K.1.1]
      have : dec.D_K / 4 = k := by omega
      rw [this]; nlinarith
    · have h0f : ¬(dec.D_K % 4 = 0) := by omega
      simp only [h0f, ↑reduceIte]
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (dec.D_K - 1) % 4 = 0 by omega)
      have hm_neg : m < 0 := by nlinarith [dec.hD_K.1.1]
      have : (dec.D_K - 1) / 4 = m := by omega
      rw [this]; nlinarith
  hdisc_mod := by
    rcases dec.hD_K.1.2 with h0 | h1
    · simp only [h0, ↑reduceIte]; left; omega
    · have h0f : ¬(dec.D_K % 4 = 0) := by omega
      simp only [h0f, ↑reduceIte]
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (dec.D_K - 1) % 4 = 0 by omega)
      have hm_eq : (dec.D_K - 1) / 4 = m := by omega
      rw [hm_eq]
      rcases (show dec.u % 2 = 0 ∨ dec.u % 2 = 1 by omega) with hu | hu
      · left
        obtain ⟨j, hj⟩ := Int.dvd_of_emod_eq_zero hu
        have : dec.u ^ 2 - 4 * -(dec.u ^ 2 * m) = dec.u ^ 2 * (4 * m + 1) := by ring
        rw [this, hj]; ring_nf; omega
      · right
        obtain ⟨j, hj⟩ := Int.dvd_of_emod_eq_zero (show (dec.u - 1) % 2 = 0 by omega)
        have hu_eq : dec.u = 2 * j + 1 := by omega
        have : dec.u ^ 2 - 4 * -(dec.u ^ 2 * m) = dec.u ^ 2 * (4 * m + 1) := by ring
        rw [this, hu_eq]; ring_nf; omega

/-- The order built by `orderFromDecomposition` has discriminant equal to `D`. -/
theorem orderFromDecomposition_disc {D : ℤ}
    (dec : ImaginaryQuadraticDiscriminantDecomposition D) :
    (orderFromDecomposition dec).discriminant = D := by
  simp only [orderFromDecomposition, ImaginaryQuadraticOrder.discriminant]
  rcases dec.hD_K.1.2 with h0 | h1
  · simp only [h0, ↑reduceIte]
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
    have hk_eq : dec.D_K / 4 = k := by omega
    rw [hk_eq]
    nlinarith [dec.hD, hk]
  · have h0f : ¬(dec.D_K % 4 = 0) := by omega
    simp only [h0f, ↑reduceIte]
    obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (dec.D_K - 1) % 4 = 0 by omega)
    have hm_eq : (dec.D_K - 1) / 4 = m := by omega
    rw [hm_eq]
    nlinarith [dec.hD]

/-- The maximal order of an imaginary quadratic field with fundamental discriminant `D_K`,
constructed as an `ImaginaryQuadraticOrder`. -/
def maximalOrder (D_K : ℤ) (hfund : IsFundamentalImaginaryQuadraticDiscriminant D_K) :
    ImaginaryQuadraticOrder where
  t := if D_K % 4 = 0 then 0 else 1
  n := if D_K % 4 = 0 then -(D_K / 4) else -((D_K - 1) / 4)
  hdisc_neg := by
    rcases hfund.1.2 with h0 | h1
    · simp only [h0, ↑reduceIte]
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
      have : D_K / 4 = k := by omega
      rw [this]; nlinarith [hfund.1.1]
    · have h0f : ¬(D_K % 4 = 0) := by omega
      simp only [h0f, ↑reduceIte]
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (D_K - 1) % 4 = 0 by omega)
      have : (D_K - 1) / 4 = m := by omega
      rw [this]; nlinarith [hfund.1.1]
  hdisc_mod := by
    rcases hfund.1.2 with h0 | h1
    · simp only [h0, ↑reduceIte]; left; omega
    · have h0f : ¬(D_K % 4 = 0) := by omega
      simp only [h0f, ↑reduceIte]; right
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (D_K - 1) % 4 = 0 by omega)
      have : (D_K - 1) / 4 = m := by omega
      rw [this]; omega

/-- The maximal order constructed by `maximalOrder` has the prescribed discriminant `D_K`. -/
theorem maximalOrder_disc (D_K : ℤ)
    (hfund : IsFundamentalImaginaryQuadraticDiscriminant D_K) :
    (maximalOrder D_K hfund).discriminant = D_K := by
  simp only [maximalOrder, ImaginaryQuadraticOrder.discriminant]
  rcases hfund.1.2 with h0 | h1
  · simp only [h0, ↑reduceIte]
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
    have : D_K / 4 = k := by omega
    rw [this]; nlinarith [hk]
  · have h0f : ¬(D_K % 4 = 0) := by omega
    simp only [h0f, ↑reduceIte]
    obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (D_K - 1) % 4 = 0 by omega)
    have : (D_K - 1) / 4 = m := by omega
    rw [this]; nlinarith

/-- The conductor relation: the discriminant of `orderFromDecomposition dec` is `u²` times
the discriminant of the maximal order with fundamental discriminant `D_K`. -/
theorem conductor_eq {D : ℤ}
    (dec : ImaginaryQuadraticDiscriminantDecomposition D) :
    (orderFromDecomposition dec).discriminant =
      dec.u ^ 2 * (maximalOrder dec.D_K dec.hD_K).discriminant := by
  rw [orderFromDecomposition_disc, maximalOrder_disc]
  exact dec.hD

/-- Existence and uniqueness: every imaginary quadratic discriminant `D` factors uniquely
as `u² · D_K`, giving rise to a maximal order `𝒪_K` and a unique (up to `SameOrder`)
order `𝒪` of discriminant `D`. -/
theorem exists_unique_order (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    ∃ (u D_K : ℤ), u ≥ 1 ∧ IsFundamentalImaginaryQuadraticDiscriminant D_K ∧
      D = u ^ 2 * D_K ∧
      ∃ (𝒪_K : ImaginaryQuadraticOrder), 𝒪_K.discriminant = D_K ∧
      ∃ (𝒪 : ImaginaryQuadraticOrder), 𝒪.discriminant = D ∧
        𝒪.discriminant = u ^ 2 * 𝒪_K.discriminant ∧
        (∀ 𝒪' : ImaginaryQuadraticOrder, 𝒪'.discriminant = D → 𝒪.SameOrder 𝒪') := by
  obtain ⟨D_K, u, hu, hfund, hdecomp⟩ := discriminant_decomposition_exists D hD
  let dec : ImaginaryQuadraticDiscriminantDecomposition D := ⟨u, D_K, hu, hfund, hdecomp⟩
  refine ⟨u, D_K, hu, hfund, hdecomp, maximalOrder D_K hfund, maximalOrder_disc D_K hfund,
    orderFromDecomposition dec, orderFromDecomposition_disc dec, ?_, fun 𝒪' h𝒪' =>
      uniqueness _ 𝒪' ((orderFromDecomposition_disc dec).trans h𝒪'.symm)⟩
  rw [orderFromDecomposition_disc dec, maximalOrder_disc]
  exact hdecomp

/-- `𝒪` is a suborder of `𝒪_K` with index `u` if its discriminant is `u²` times that of
`𝒪_K` and the traces satisfy `𝒪.t = 2a + u · 𝒪_K.t` for some integer `a`. -/
def ImaginaryQuadraticOrder.IsSuborderOfIndex (𝒪 𝒪_K : ImaginaryQuadraticOrder) (u : ℤ) : Prop :=
  u ≥ 1 ∧ 𝒪.discriminant = u ^ 2 * 𝒪_K.discriminant ∧
  ∃ a : ℤ, 𝒪.t = 2 * a + u * 𝒪_K.t

/-- The order constructed from a decomposition is a suborder of index `u` of the maximal
order of `D_K`. -/
theorem conductor_is_lattice_index {D : ℤ}
    (dec : ImaginaryQuadraticDiscriminantDecomposition D) :
    (orderFromDecomposition dec).IsSuborderOfIndex (maximalOrder dec.D_K dec.hD_K) dec.u := by
  refine ⟨dec.hu, by rw [orderFromDecomposition_disc, maximalOrder_disc]; exact dec.hD, ?_⟩


  simp only [orderFromDecomposition, maximalOrder]
  rcases dec.hD_K.1.2 with h0 | h1
  ·
    simp only [h0, ↑reduceIte]
    exact ⟨0, by ring⟩
  ·
    have h0f : ¬(dec.D_K % 4 = 0) := by omega
    simp only [h0f, ↑reduceIte]
    exact ⟨0, by ring⟩

/-- Refined existence-uniqueness statement: every imaginary quadratic discriminant `D`
gives rise to a unique pair `(𝒪_K, 𝒪)` with `𝒪 ⊂ 𝒪_K` of conductor index `u`. -/
theorem exists_unique_order_conductor_index (D : ℤ)
    (hD : IsImaginaryQuadraticDiscriminant D) :
    ∃ (u D_K : ℤ) (𝒪_K 𝒪 : ImaginaryQuadraticOrder),
      u ≥ 1 ∧ IsFundamentalImaginaryQuadraticDiscriminant D_K ∧
      𝒪_K.discriminant = D_K ∧ 𝒪.discriminant = D ∧
      𝒪.IsSuborderOfIndex 𝒪_K u ∧
      (∀ 𝒪' : ImaginaryQuadraticOrder, 𝒪'.discriminant = D → 𝒪.SameOrder 𝒪') := by
  obtain ⟨D_K, u, hu, hfund, hdecomp⟩ := discriminant_decomposition_exists D hD
  let dec : ImaginaryQuadraticDiscriminantDecomposition D := ⟨u, D_K, hu, hfund, hdecomp⟩
  refine ⟨u, D_K, maximalOrder D_K hfund, orderFromDecomposition dec,
    hu, hfund, maximalOrder_disc D_K hfund, orderFromDecomposition_disc dec,
    conductor_is_lattice_index dec, fun 𝒪' h𝒪' =>
      uniqueness _ 𝒪' ((orderFromDecomposition_disc dec).trans h𝒪'.symm)⟩

end ImagQuadDiscriminant

namespace ProperIdealInvertible

open FractionalIdeal

section General

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The order (multiplier ring) of a fractional ideal `I` in `K`: the set of `x : K` such
that `x · I ⊆ I`. -/
def idealOrder (I : FractionalIdeal R⁰ K) : Set K :=
  {x : K | ∀ y ∈ (I : Submodule R K), x * y ∈ (I : Submodule R K)}

/-- A fractional ideal `I` is *proper* if its order equals the image of `R` in `K`, i.e.
its multiplier ring is exactly `R` itself. -/
def IsProper (I : FractionalIdeal R⁰ K) : Prop :=
  idealOrder I = Set.range (algebraMap R K)

omit [IsDomain R] [IsFractionRing R K] in
/-- `R` always sits inside the order of any fractional ideal: `R ⊆ idealOrder I`. -/
theorem algebraMap_range_subset_idealOrder (I : FractionalIdeal R⁰ K) :
    Set.range (algebraMap R K) ⊆ idealOrder I := by
  rintro x ⟨r, rfl⟩ y hy
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact Submodule.smul_mem _ r hy

omit [IsDomain R] [IsFractionRing R K] in
/-- Reformulation of `IsProper`: properness is equivalent to the reverse inclusion
`idealOrder I ⊆ R`. -/
theorem isProper_iff_order_subset (I : FractionalIdeal R⁰ K) :
    IsProper I ↔ idealOrder I ⊆ Set.range (algebraMap R K) :=
  ⟨fun h => h ▸ le_refl _, fun h => le_antisymm h (algebraMap_range_subset_idealOrder I)⟩

set_option linter.unusedSectionVars false in
/-- Multiplying by an invertible fractional ideal does not change the order: `idealOrder
(u · I) = idealOrder I` for a unit `u`. -/
lemma idealOrder_mul_unit (u : (FractionalIdeal R⁰ K)ˣ) (I : FractionalIdeal R⁰ K) :
    idealOrder ((u : FractionalIdeal R⁰ K) * I) = idealOrder I := by
  ext x
  simp only [idealOrder, Set.mem_setOf_eq]
  rw [show (∀ y ∈ ((↑u * I : FractionalIdeal R⁰ K) : Submodule R K),
        x * y ∈ ((↑u * I : FractionalIdeal R⁰ K) : Submodule R K)) ↔
      spanSingleton R⁰ x * (↑u * I) ≤ ↑u * I
    from spanSingleton_mul_le_iff.symm]
  rw [show (∀ y ∈ (I : Submodule R K), x * y ∈ (I : Submodule R K)) ↔
      spanSingleton R⁰ x * I ≤ I
    from spanSingleton_mul_le_iff.symm]
  constructor
  · intro h
    have hcomm : spanSingleton R⁰ x * (↑u * I) = ↑u * (spanSingleton R⁰ x * I) := by ring
    rw [hcomm] at h
    have h1 : ↑u⁻¹ * (↑u * (spanSingleton R⁰ x * I)) ≤ ↑u⁻¹ * (↑u * I) :=
      mul_le_mul_of_nonneg_left h (FractionalIdeal.zero_le _)
    simp only [← mul_assoc] at h1
    have h2 : (↑u⁻¹ : FractionalIdeal R⁰ K) * ↑u = 1 := by exact_mod_cast u.inv_mul
    rw [h2, one_mul, one_mul] at h1
    exact h1
  · intro h
    have hcomm : spanSingleton R⁰ x * (↑u * I) = ↑u * (spanSingleton R⁰ x * I) := by ring
    rw [hcomm]
    exact mul_le_mul_of_nonneg_left h (FractionalIdeal.zero_le _)

set_option linter.unusedSectionVars false in
/-- Properness is preserved under multiplication by a unit: `IsProper (u · I) ↔
IsProper I`. -/
lemma isProper_mul_unit_iff (u : (FractionalIdeal R⁰ K)ˣ) (I : FractionalIdeal R⁰ K) :
    IsProper ((u : FractionalIdeal R⁰ K) * I) ↔ IsProper I := by
  unfold IsProper
  rw [idealOrder_mul_unit]

omit [IsDomain R] in
/-- Every invertible (unit) fractional ideal is proper. -/
theorem isProper_of_isUnit (I : FractionalIdeal R⁰ K) (hI : IsUnit I) :
    IsProper I := by
  rw [isProper_iff_order_subset]
  intro x hx
  obtain ⟨u, rfl⟩ := hI
  have h1 : spanSingleton R⁰ x * ↑u ≤ ↑u := by
    rw [FractionalIdeal.mul_le]
    intro a ha b hb
    rw [FractionalIdeal.mem_spanSingleton] at ha
    obtain ⟨c, rfl⟩ := ha
    exact (Algebra.smul_mul_assoc c x b) ▸ Submodule.smul_mem _ c (hx b hb)
  have h2 : spanSingleton R⁰ x * ↑u * ↑u⁻¹ ≤ ↑u * ↑u⁻¹ :=
    mul_le_mul_of_nonneg_right h1 (FractionalIdeal.zero_le _)
  rw [mul_assoc, u.mul_inv, mul_one] at h2
  rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_one_iff] at h2
  exact h2.elim (fun r hr => ⟨r, hr⟩)

end General

section Quadratic

variable {d : ℤ}

/-- The canonical `ℤ`-linear equivalence `ℤ√d ≃ₗ[ℤ] (Fin 2 → ℤ)` sending `α` to
`![α.re, α.im]`. Exhibits `ℤ√d` as a free `ℤ`-module of rank 2. -/
noncomputable def zsqrtdLinearEquivFin2 (d : ℤ) : (ℤ√d) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![x.re, x.im]
  invFun v := ⟨v 0, v 1⟩
  map_add' x y := by ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  map_smul' r x := by ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  left_inv x := by ext <;> simp
  right_inv v := by ext i; fin_cases i <;> simp

/-- `ℤ√d` is free as a `ℤ`-module, via the equivalence with `Fin 2 → ℤ`. -/
noncomputable instance instModuleFreeZsqrtd : Module.Free ℤ (ℤ√d) :=
  Module.Free.of_equiv (zsqrtdLinearEquivFin2 d).symm

/-- `ℤ√d` is finitely generated as a `ℤ`-module (in fact rank 2). -/
noncomputable instance instModuleFiniteZsqrtd : Module.Finite ℤ (ℤ√d) :=
  Module.Finite.equiv (zsqrtdLinearEquivFin2 d).symm

/-- The conjugate of an ideal `I ⊆ ℤ√d`: the image of `I` under the conjugation ring
homomorphism `star`. -/
def conjIdeal (I : Ideal (ℤ√d)) : Ideal (ℤ√d) :=
  Ideal.map (starRingEnd (ℤ√d)) I

/-- If `x ∈ I`, then `star x ∈ conjIdeal I`. -/
theorem mem_conjIdeal {I : Ideal (ℤ√d)} {x : ℤ√d} (hx : x ∈ I) :
    star x ∈ conjIdeal I :=
  Ideal.mem_map_of_mem _ hx

/-- Conjugation of ideals is an involution: `conjIdeal (conjIdeal I) = I`. -/
theorem conjIdeal_conjIdeal (I : Ideal (ℤ√d)) :
    conjIdeal (conjIdeal I) = I := by
  simp only [conjIdeal, Ideal.map_map]
  have : (starRingEnd (ℤ√d)).comp (starRingEnd (ℤ√d)) = RingHom.id _ := by ext <;> simp
  rw [this, Ideal.map_id]

/-- The ideal norm in `ℤ√d`, given by the cardinality of the quotient `(ℤ√d) / I`. -/
noncomputable def idealNormZsqrtd (I : Ideal (ℤ√d)) : ℕ :=
  Nat.card ((ℤ√d) ⧸ I)


/-- If `J · J' = (n)` with `n ≠ 0`, then `J` is invertible as a fractional ideal in the
field of fractions. -/
lemma isUnit_coeIdeal_of_mul_eq_span [IsDomain (ℤ√d)]
    (K' : Type*) [Field K'] [Algebra (ℤ√d) K'] [IsFractionRing (ℤ√d) K']
    (J J' : Ideal (ℤ√d)) (n : ℤ√d) (hn : n ≠ 0)
    (h : J * J' = Ideal.span {n}) :
    IsUnit ((J : FractionalIdeal (ℤ√d)⁰ K')) := by
  have h1 : (J : FractionalIdeal (ℤ√d)⁰ K') * ↑J' =
      spanSingleton (ℤ√d)⁰ ((algebraMap (ℤ√d) K') n) := by
    rw [← coeIdeal_mul, h, coeIdeal_span_singleton]
  have hn' : (algebraMap (ℤ√d) K') n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (ℤ√d) K')).mpr hn
  set inv := spanSingleton (ℤ√d)⁰ ((algebraMap (ℤ√d) K') n)⁻¹ *
    (↑J' : FractionalIdeal (ℤ√d)⁰ K')
  have h2 : (J : FractionalIdeal (ℤ√d)⁰ K') * inv = 1 := by
    calc (J : FractionalIdeal (ℤ√d)⁰ K') * inv
        = (↑J : FractionalIdeal (ℤ√d)⁰ K') * ↑J' *
          spanSingleton (ℤ√d)⁰ ((algebraMap (ℤ√d) K') n)⁻¹ := by ring
      _ = spanSingleton (ℤ√d)⁰ ((algebraMap (ℤ√d) K') n) *
          spanSingleton (ℤ√d)⁰ ((algebraMap (ℤ√d) K') n)⁻¹ := by rw [h1]
      _ = 1 := by
          rw [spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hn', spanSingleton_one]
  have h3 : inv * (J : FractionalIdeal (ℤ√d)⁰ K') = 1 := by rw [mul_comm]; exact h2
  exact ⟨⟨↑J, inv, h2, h3⟩, rfl⟩



/-- Norm of a fractional ideal in `ℤ√d`: `N(𝔞) = N(𝔞.num) / |N(𝔞.den)|`, as a rational
number. -/
noncomputable def fractionalIdealNormZsqrtd (hd : d < 0) [IsDomain (ℤ√d)]
    (K : Type*) [Field K] [Algebra (ℤ√d) K] [IsFractionRing (ℤ√d) K]
    (𝔞 : FractionalIdeal (ℤ√d)⁰ K) : ℚ :=
  (idealNormZsqrtd 𝔞.num : ℚ) / |(Zsqrtd.norm (𝔞.den : ℤ√d) : ℚ)|


end Quadratic

end ProperIdealInvertible

namespace IdealClassGroup

open nonZeroDivisors FractionalIdeal

section General

variable (R : Type*) [CommRing R] [IsDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K]

/-- The group of invertible fractional ideals of `R` in its field of fractions `K`. -/
abbrev InvertibleFractionalIdeals := (FractionalIdeal R⁰ K)ˣ

/-- The subgroup of principal invertible fractional ideals (image of `K*` under
`toPrincipalIdeal`). -/
abbrev PrincipalFractionalIdeals := (toPrincipalIdeal R K).range

/-- The subgroup of principal fractional ideals is normal in the group of invertible
fractional ideals (the ambient group is abelian). -/
instance : (PrincipalFractionalIdeals R K).Normal :=
  PrincipalIdeals.normal

/-- Identification of the quotient
`InvertibleFractionalIdeals / PrincipalFractionalIdeals` with the ideal class group
`Cl(R)` (via Mathlib's `ClassGroup.equiv`). -/
noncomputable def classGroup_mulEquiv :
    InvertibleFractionalIdeals R K ⧸ PrincipalFractionalIdeals R K ≃* ClassGroup R :=
  (ClassGroup.equiv K).symm

/-- The quotient of invertible fractional ideals by principal ones inherits an abelian
group structure. -/
noncomputable instance instCommGroupQuotient :
    CommGroup (InvertibleFractionalIdeals R K ⧸ PrincipalFractionalIdeals R K) :=
  QuotientGroup.Quotient.commGroup _

/-- The class group `Cl(R)` is an abelian group. -/
noncomputable instance : CommGroup (ClassGroup R) := inferInstance

end General

section ImaginaryQuadratic

open ProperIdealInvertible

variable {d : ℤ}


/-- Every invertible fractional ideal (in the imaginary quadratic case) is proper. -/
theorem isProper_of_isUnit_quadratic
    {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K]
    (I : FractionalIdeal R⁰ K) (hI : IsUnit I) :
    IsProper I :=
  isProper_of_isUnit I hI

/-- Identification of the quotient
`InvertibleFractionalIdeals(ℤ√d) / PrincipalFractionalIdeals(ℤ√d)` with the class group
`Cl(ℤ√d)` (in the imaginary quadratic case). -/
noncomputable def classGroupQuotient_imaginaryQuadratic
    [IsDomain (ℤ√d)]
    (K : Type*) [Field K] [Algebra (ℤ√d) K] [IsFractionRing (ℤ√d) K] :
    (FractionalIdeal (ℤ√d)⁰ K)ˣ ⧸ (toPrincipalIdeal (ℤ√d) K).range ≃*
    ClassGroup (ℤ√d) :=
  classGroup_mulEquiv (ℤ√d) K

end ImaginaryQuadratic

section ClassGroupQuotientEquiv

open ComplexLattice

variable (𝒪 : Subring ℂ) [IsDomain 𝒪]



/-- Specialised version for `𝒪 = ℤ√d`: the quotient
`(FractionalIdeal (ℤ√d) K)ˣ / Principal` is `Cl(ℤ√d)`. -/
noncomputable def classGroupQuotient_Zsqrtd (d : ℤ) [IsDomain (ℤ√d)]
    (K : Type*) [Field K] [Algebra (ℤ√d) K] [IsFractionRing (ℤ√d) K] :
    (FractionalIdeal (ℤ√d)⁰ K)ˣ ⧸ (toPrincipalIdeal (ℤ√d) K).range ≃*
    ClassGroup (ℤ√d) :=
  classGroup_mulEquiv (ℤ√d) K

end ClassGroupQuotientEquiv

end IdealClassGroup

namespace IdealTorsion

variable {𝒪 : Type*} [CommRing 𝒪]
variable {E : Type*} [AddCommGroup E] [Module 𝒪 E]

/-- The `𝔞`-torsion submodule of an `𝒪`-module `E`: the set of `P ∈ E` such that
`α · P = 0` for every `α ∈ 𝔞`. -/
def idealTorsion (𝔞 : Ideal 𝒪) : Submodule 𝒪 E where
  carrier := {P : E | ∀ α ∈ 𝔞, α • P = 0}
  zero_mem' := fun α _ => smul_zero α
  add_mem' := fun {P Q} hP hQ α hα => by rw [smul_add, hP α hα, hQ α hα, add_zero]
  smul_mem' := fun r {P} hP α hα => by
    rw [smul_comm]
    exact smul_eq_zero_of_right r (hP α hα)

/-- Defining property of `idealTorsion`: `P ∈ idealTorsion 𝔞` iff `α · P = 0` for all
`α ∈ 𝔞`. -/
@[simp]
theorem mem_idealTorsion_iff (𝔞 : Ideal 𝒪) (P : E) :
    P ∈ idealTorsion 𝔞 ↔ ∀ α ∈ 𝔞, α • P = 0 :=
  Iff.rfl

/-- The bespoke `idealTorsion` agrees with Mathlib's `Submodule.torsionBySet`. -/
@[simp]
theorem idealTorsion_eq_torsionBySet (𝔞 : Ideal 𝒪) :
    idealTorsion (E := E) 𝔞 = Submodule.torsionBySet 𝒪 E (𝔞 : Set 𝒪) := by
  ext P
  simp only [mem_idealTorsion_iff, Submodule.mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall]

/-- The `𝔞`-torsion submodule viewed as an additive subgroup of `E`. -/
def idealTorsionAddSubgroup (𝔞 : Ideal 𝒪) : AddSubgroup E :=
  (idealTorsion 𝔞).toAddSubgroup

end IdealTorsion

namespace CMTorsorAction

open IdealTorsion NormTrace

variable {𝒪 : Type*} [CommRing 𝒪]

/-- A *CM-module* over `𝒪` is an `𝒪`-module `E` together with the data of an ideal
`latticeIdeal ⊆ 𝒪` and an `𝒪`-linear equivalence `E ≃ₗ[𝒪] 𝒪 / latticeIdeal`. -/
class IsCMModule (𝒪 : Type*) [CommRing 𝒪] (E : Type*) [AddCommGroup E] [Module 𝒪 E] where
  latticeIdeal : Ideal 𝒪
  linearEquiv : E ≃ₗ[𝒪] 𝒪 ⧸ (latticeIdeal : Submodule 𝒪 𝒪)

/-- Data describing a CM-isogeny `𝒪/𝔟 → 𝒪/targetIdeal` corresponding to multiplication by
an ideal `𝔞`: includes the target ideal (the colon ideal `(𝔟 : 𝔞)`) and the relation
`𝔞 · targetIdeal = 𝔟`. -/
structure CMIsogenyData (𝒪 : Type*) [CommRing 𝒪] (𝔟 : Ideal 𝒪) (𝔞 : Ideal 𝒪) where
  targetIdeal : Ideal 𝒪
  le_target : 𝔟 ≤ targetIdeal
  ideal_mul_target_le : 𝔞 * targetIdeal ≤ 𝔟
  target_eq_colon :
    (targetIdeal : Submodule 𝒪 𝒪) = (𝔟 : Submodule 𝒪 𝒪).colon (𝔞 : Set 𝒪)
  ideal_mul_target_eq : 𝔞 * targetIdeal = 𝔟

/-- The `𝒪`-linear map `𝒪/𝔟 → 𝒪/targetIdeal` underlying a `CMIsogenyData`. -/
noncomputable def CMIsogenyData.toLinearMap {𝔟 𝔞 : Ideal 𝒪} (φ : CMIsogenyData 𝒪 𝔟 𝔞) :
    (𝒪 ⧸ (𝔟 : Submodule 𝒪 𝒪)) →ₗ[𝒪] (𝒪 ⧸ (φ.targetIdeal : Submodule 𝒪 𝒪)) :=
  (𝔟 : Submodule 𝒪 𝒪).mapQ φ.targetIdeal LinearMap.id
    (by rw [Submodule.comap_id]; exact φ.le_target)

/-- The linear map associated to a `CMIsogenyData` is surjective. -/
theorem CMIsogenyData.toLinearMap_surjective {𝔟 𝔞 : Ideal 𝒪} (φ : CMIsogenyData 𝒪 𝔟 𝔞) :
    Function.Surjective φ.toLinearMap := by
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- The kernel of `φ.toLinearMap` is the image of the target ideal inside `𝒪/𝔟`. -/
theorem CMIsogenyData.ker_toLinearMap {𝔟 𝔞 : Ideal 𝒪} (φ : CMIsogenyData 𝒪 𝔟 𝔞) :
    LinearMap.ker φ.toLinearMap =
      Submodule.map (𝔟 : Submodule 𝒪 𝒪).mkQ (φ.targetIdeal : Submodule 𝒪 𝒪) := by
  unfold CMIsogenyData.toLinearMap
  rw [Submodule.ker_mapQ]
  simp only [Submodule.comap_id]

/-- The degree of the CM-isogeny `φ`, defined as the cardinality of its kernel. -/
noncomputable def degIsogeny {𝔟 𝔞 : Ideal 𝒪} (φ : CMIsogenyData 𝒪 𝔟 𝔞) : ℕ :=
  Nat.card (LinearMap.ker φ.toLinearMap)

/-- The degree of the CM-isogeny equals the ideal norm of `𝔞`, provided the target ideal
is nonzero (so that the quotient is finite). -/
theorem degIsogeny_eq_idealNorm {𝔟 𝔞 : Ideal 𝒪}
    [IsDedekindDomain 𝒪] [Module.Free ℤ 𝒪] [Module.Finite ℤ 𝒪]
    (φ : CMIsogenyData 𝒪 𝔟 𝔞)
    (h𝔠_ne : φ.targetIdeal ≠ ⊥) :
    degIsogeny φ = idealNorm 𝔞 := by
  unfold degIsogeny idealNorm
  rw [φ.ker_toLinearMap]

  have h3 := Submodule.card_quotient_mul_card_quotient
    (φ.targetIdeal : Submodule 𝒪 𝒪) (𝔟 : Submodule 𝒪 𝒪) φ.le_target

  have hcm := cardQuot_mul 𝔞 φ.targetIdeal
  rw [φ.ideal_mul_target_eq] at hcm
  simp only [Submodule.cardQuot_apply] at hcm
  rw [hcm] at h3

  have hfin : Finite (𝒪 ⧸ φ.targetIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot φ.targetIdeal h𝔠_ne
  have h𝔠_pos : 0 < Nat.card (𝒪 ⧸ (φ.targetIdeal : Submodule 𝒪 𝒪)) := by
    rw [Nat.card_pos_iff]
    exact ⟨inferInstance, inferInstance⟩
  exact mul_right_cancel₀ (Nat.pos_iff_ne_zero.mp h𝔠_pos) h3

end CMTorsorAction

namespace CMIdealIsogeny

open CMTorsorAction NormTrace

variable {𝒪 : Type*} [CommRing 𝒪]

/-- Restatement: the degree of a CM-isogeny coincides with the ideal norm of the
acting ideal. -/
theorem isogeny_degree_eq_idealNorm {𝔟 𝔞 : Ideal 𝒪}
    [IsDedekindDomain 𝒪] [Module.Free ℤ 𝒪] [Module.Finite ℤ 𝒪]
    (φ : CMIsogenyData 𝒪 𝔟 𝔞)
    (h𝔠_ne : φ.targetIdeal ≠ ⊥) :
    degIsogeny φ = idealNorm 𝔞 :=
  degIsogeny_eq_idealNorm φ h𝔠_ne


end CMIdealIsogeny
