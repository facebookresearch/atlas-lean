/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.KummerDedekind
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

open nonZeroDivisors DirectSum


section LocalModuleIndex

variable {R : Type*} [CommRing R] [IsDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {M : Type*} [AddCommGroup M] [Module R M]

noncomputable def localModuleIndex (φ : M →ₗ[R] M) : FractionalIdeal R⁰ K :=
  FractionalIdeal.spanSingleton R⁰ (algebraMap R K (LinearMap.det φ))

theorem localModuleIndex_comp_equiv (φ : M →ₗ[R] M) (u v : M ≃ₗ[R] M) :
    localModuleIndex (K := K) ((u : M →ₗ[R] M) ∘ₗ φ ∘ₗ (v : M →ₗ[R] M)) =
    localModuleIndex (K := K) φ := by
  simp only [localModuleIndex, LinearMap.det_comp, map_mul]
  rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
  refine ⟨(LinearEquiv.det u)⁻¹ * (LinearEquiv.det v)⁻¹, ?_⟩
  simp only [Units.smul_def, Units.val_mul, Algebra.smul_def, ← LinearEquiv.coe_det, ← map_mul]
  congr 1
  have hu := Units.inv_mul (LinearEquiv.det u)
  have hv := Units.inv_mul (LinearEquiv.det v)
  calc ↑(LinearEquiv.det u)⁻¹ * ↑(LinearEquiv.det v)⁻¹ *
      (↑(LinearEquiv.det u) * (LinearMap.det φ * ↑(LinearEquiv.det v)))
      = (↑(LinearEquiv.det u)⁻¹ * ↑(LinearEquiv.det u)) *
        (↑(LinearEquiv.det v)⁻¹ * ↑(LinearEquiv.det v)) * LinearMap.det φ := by ring
    _ = 1 * 1 * LinearMap.det φ := by rw [hu, hv]
    _ = LinearMap.det φ := by ring

omit [IsDomain R] in
theorem localModuleIndex_comp (φ ψ : M →ₗ[R] M) :
    localModuleIndex (K := K) (φ ∘ₗ ψ) =
    localModuleIndex (K := K) φ * localModuleIndex (K := K) ψ := by
  simp only [localModuleIndex, LinearMap.det_comp, map_mul,
    FractionalIdeal.spanSingleton_mul_spanSingleton]

omit [IsDomain R] in
@[simp]
theorem localModuleIndex_id :
    localModuleIndex (K := K) (LinearMap.id : M →ₗ[R] M) = 1 := by
  simp [localModuleIndex, LinearMap.det_id, map_one, FractionalIdeal.spanSingleton_one]

end LocalModuleIndex

section GlobalModuleIndex

lemma prod_ne_zero_of_ne_bot
    {A : Type*} [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {n : ℕ} (J : Fin n → Ideal A) (hJ : ∀ i, J i ≠ ⊥) :
    (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K) ≠ 0 := by
  rw [FractionalIdeal.coeIdeal_ne_zero]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, Ne, Ideal.mul_eq_bot]
    push Not
    exact ⟨ih (J ∘ Fin.castSucc) (fun i => hJ (Fin.castSucc i)), hJ (Fin.last n)⟩























end GlobalModuleIndex

section CyclicQuotient


end CyclicQuotient


section ConcreteModuleIndex

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

noncomputable def concreteModuleIndex (N : Submodule R M) : ℕ :=
  Nat.card (M ⧸ N)

theorem concreteModuleIndex_eq_cardQuot (N : Submodule R M) :
    concreteModuleIndex N = Submodule.cardQuot N :=
  (Submodule.cardQuot_apply N).symm

@[simp]
theorem concreteModuleIndex_top :
    concreteModuleIndex (⊤ : Submodule R M) = 1 := by
  rw [concreteModuleIndex_eq_cardQuot, Submodule.cardQuot_top]

theorem concreteModuleIndex_mul_tower (N P : Submodule R M) (hPN : P ≤ N) :
    Nat.card ↥(N.map P.mkQ) * Nat.card (M ⧸ N) = Nat.card (M ⧸ P) :=
  Submodule.card_quotient_mul_card_quotient N P hPN

theorem concreteModuleIndex_ideal_mul {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] (I J : Ideal S) :
    Nat.card (S ⧸ (I * J : Ideal S)) = Nat.card (S ⧸ I) * Nat.card (S ⧸ J) := by
  rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply]
  exact cardQuot_mul I J

end ConcreteModuleIndex

section DetFormula

variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

open Module in
theorem concreteModuleIndex_eq_natAbs_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ M) (N : Submodule ℤ M) (bN : Basis ι ℤ N) :
    (b.det ((↑) ∘ bN)).natAbs = concreteModuleIndex N :=
  Submodule.natAbs_det_basis_change b N bN

open Module in
theorem concreteModuleIndex_eq_natAbs_det_equiv (N : Submodule ℤ M) {E : Type*}
    [EquivLike E M N] [AddEquivClass E M N] (e : E) :
    Int.natAbs (LinearMap.det (N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : M →+ N))) =
      concreteModuleIndex N :=
  Submodule.natAbs_det_equiv N e

end DetFormula

section NormConcreteIndex

open NumberField

theorem idealNorm_eq_concreteModuleIndex {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) :
    Ideal.absNorm I = concreteModuleIndex (I : Submodule (𝓞 K) (𝓞 K)) := by
  rw [concreteModuleIndex, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem absNorm_mul_eq {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) :
    Ideal.absNorm (I * J) = Ideal.absNorm I * Ideal.absNorm J :=
  map_mul (Ideal.absNorm) I J

end NormConcreteIndex


open Ideal Polynomial UniqueFactorizationMonoid

namespace DedekindKummer

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain S] [Module.IsTorsionFree R S]
variable {x : S} {I : Ideal R}

attribute [local instance] Ideal.Quotient.field

open Classical in
noncomputable def dedekind_kummer_bijection
    (hI : I.IsMaximal) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) :
    {J : Ideal S | J ∈ normalizedFactors (I.map (algebraMap R S))} ≃
      {d : (R ⧸ I)[X] |
        d ∈ normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))} :=
  KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx'

open Classical in
theorem dedekind_kummer_multiplicity
    (hI : I.IsMaximal) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x)
    {J : Ideal S} (hJ : J ∈ normalizedFactors (I.map (algebraMap R S))) :
    emultiplicity J (I.map (algebraMap R S)) =
      emultiplicity
        (↑(dedekind_kummer_bijection hI hI' hx hx' ⟨J, hJ⟩))
        (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) :=
  KummerDedekind.emultiplicity_factors_map_eq_emultiplicity hI hI' hx hx' hJ

open Classical in
set_option backward.isDefEq.respectTransparency false in
theorem dedekind_kummer_prime_formula
    (hI : I.IsMaximal)
    {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk I) ∈
      normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk I)))
    (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) :
    ((dedekind_kummer_bijection hI hI' hx hx').symm ⟨_, hQ⟩).val =
      Ideal.span (↑(I.map (algebraMap R S)) ∪ {Polynomial.aeval x Q}) :=
  KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span
    hI hQ hI' hx hx'

open Classical in
set_option backward.isDefEq.respectTransparency false in
theorem dedekind_kummer
    (hI : I.IsMaximal) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) :
    normalizedFactors (I.map (algebraMap R S)) =
      Multiset.map
        (fun f =>
          ((dedekind_kummer_bijection hI hI' hx hx').symm f : Ideal S))
        (normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))).attach :=
  KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map hI hI' hx hx'

end DedekindKummer


section IdealNorm

variable (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain A]
variable {B : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
variable [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]

noncomputable def idealNorm : Ideal B →*₀ Ideal A := Ideal.relNorm A

@[simp] theorem idealNorm_def : (idealNorm A : Ideal B →*₀ Ideal A) = Ideal.relNorm A := rfl

theorem idealNorm_apply (I : Ideal B) :
    idealNorm A I = Ideal.span (Algebra.intNorm A B '' (I : Set B)) :=
  Ideal.relNorm_apply A I

@[simp] theorem idealNorm_zero : idealNorm A (0 : Ideal B) = 0 := map_zero (idealNorm A)

theorem idealNorm_ne_zero {I : Ideal B} (hI : I ≠ 0) : idealNorm A I ≠ 0 := by
  simp only [idealNorm, ne_eq]
  rw [show (0 : Ideal A) = ⊥ from rfl, Ideal.relNorm_eq_bot_iff,
      show (⊥ : Ideal B) = 0 from rfl]
  exact hI

theorem idealNorm_eq_zero_iff {I : Ideal B} : idealNorm A I = 0 ↔ I = 0 := by
  simp only [idealNorm, show (0 : Ideal A) = ⊥ from rfl, show (0 : Ideal B) = ⊥ from rfl,
    Ideal.relNorm_eq_bot_iff]

theorem idealNorm_mono {I J : Ideal B} (h : I ≤ J) : idealNorm A I ≤ idealNorm A J :=
  Ideal.relNorm_mono A h

theorem idealNorm_principal (α : B) :
    idealNorm A (Ideal.span {α}) = Ideal.span {Algebra.intNorm A B α} :=
  Ideal.relNorm_singleton A α

theorem idealNorm_principal_free [Module.Free A B] (α : B) :
    idealNorm A (Ideal.span {α}) = Ideal.span {Algebra.norm A α} := by
  rw [idealNorm_principal, Algebra.intNorm_eq_norm]

theorem idealNorm_mul (I J : Ideal B) :
    idealNorm A (I * J) = idealNorm A I * idealNorm A J :=
  map_mul (idealNorm A) I J

theorem idealNorm_one : idealNorm A (1 : Ideal B) = 1 := map_one (idealNorm A)

theorem relNorm_ne_bot_of_ne_bot
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (I : Ideal B) (_ : I ≠ ⊥) :
    Ideal.relNorm A I ≠ ⊥ := by
  rwa [ne_eq, Ideal.relNorm_eq_bot_iff]














end IdealNorm


section IdealNorm

variable (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain A]
variable {B : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
variable [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]






theorem idealNorm_eq_span_norms (I : Ideal B) :
    idealNorm A I = Ideal.span (Algebra.intNorm A B '' (I : Set B)) :=
  Ideal.relNorm_apply A I

theorem idealNorm_eq_span_fieldNorms [Module.Free A B] (I : Ideal B) :
    idealNorm A I = Ideal.span (Algebra.norm A '' (I : Set B)) := by
  rw [idealNorm_eq_span_norms]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, by rw [Algebra.intNorm_eq_norm]⟩
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, by rw [Algebra.intNorm_eq_norm]⟩

end IdealNorm



section IdealNormPrime

variable {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain A]
variable {B : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
variable [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]

theorem idealNorm_prime [PerfectField (FractionRing A)]
    (Q : Ideal B) (p : Ideal A) [Q.LiesOver p] [Q.IsMaximal] [p.IsMaximal] :
    idealNorm A Q = p ^ p.inertiaDeg Q :=
  Ideal.relNorm_eq_pow_of_isMaximal Q p

attribute [local instance] FractionRing.liftAlgebra in
theorem idealNorm_map_eq_pow (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [IsDedekindDomain B] [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (I : Ideal A) :
    idealNorm A (I.map (algebraMap A B)) =
      I ^ Module.finrank (FractionRing A) (FractionRing B) :=
  Ideal.relNorm_algebraMap B I

end IdealNormPrime


section NormNumberField

open NumberField

theorem absNorm_eq_card_quot {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) :
    Ideal.absNorm I = Nat.card ((𝓞 K) ⧸ I) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem absNorm_mul_card_quotient_eq {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hle : J ≤ I) :
    Ideal.absNorm I *
      Nat.card (Submodule.map (Submodule.mkQ (J : Submodule (𝓞 K) (𝓞 K)))
        (I : Submodule (𝓞 K) (𝓞 K))) =
    Ideal.absNorm J := by
  rw [mul_comm, Ideal.absNorm_apply, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Submodule.card_quotient_mul_card_quotient _ _ hle

theorem moduleIndex_eq_absNorm_quotient {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hle : J ≤ I)
    (C : Ideal (𝓞 K)) (hC : J = I * C) :
    Nat.card (Submodule.map (Submodule.mkQ (J : Submodule (𝓞 K) (𝓞 K)))
        (I : Submodule (𝓞 K) (𝓞 K))) =
    Ideal.absNorm C := by
  have tower := absNorm_mul_card_quotient_eq I J hle
  have mul_norm : Ideal.absNorm J = Ideal.absNorm I * Ideal.absNorm C := by
    rw [hC, map_mul]
  have hI_pos : 0 < Ideal.absNorm I :=
    Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  exact Nat.eq_of_mul_eq_mul_left hI_pos (tower.trans mul_norm)

end NormNumberField

namespace DedekindKummer.NF

open Ideal Polynomial UniqueFactorizationMonoid KummerDedekind NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {p : ℕ} [Fact (Nat.Prime p)]

theorem inertiaDeg_eq_natDegree
    (hp : ¬ p ∣ RingOfIntegers.exponent θ)
    {Q : (ZMod p)[X]}
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod θ p) :
    inertiaDeg (span {(p : ℤ)})
      ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
        Q.natDegree :=
  NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ

theorem ramificationIdx_eq_multiplicity
    (hp : ¬ p ∣ RingOfIntegers.exponent θ)
    {Q : (ZMod p)[X]}
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod θ p) :
    (span {(p : ℤ)}).ramificationIdx
      ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
        multiplicity Q ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) :=
  NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ

end DedekindKummer.NF
