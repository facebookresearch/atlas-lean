/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.NumberTheoryI.code.KroneckerWeber
import Atlas.NumberTheoryI.code.IdealFactorization
import Atlas.NumberTheoryI.code.FinitePlaceAbsValue
noncomputable section

open scoped NumberField

namespace RayClassField

inductive Place (K : Type*) [Field K] [NumberField K] where
  | finite : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → Place K
  | infinite : NumberField.InfinitePlace K → Place K

variable {K : Type*} [Field K] [NumberField K]

def Place.isFinite : Place K → Prop
  | Place.finite _ => True
  | Place.infinite _ => False

structure Modulus (K : Type*) [Field K] [NumberField K] where
  toFun : Place K → ℕ
  finite_support : Set.Finite {v | toFun v ≠ 0}
  inf_le_one : ∀ v : NumberField.InfinitePlace K, toFun (Place.infinite v) ≤ 1
  complex_zero : ∀ v : NumberField.InfinitePlace K, v.IsComplex → toFun (Place.infinite v) = 0

instance : CoeFun (Modulus K) (fun _ => Place K → ℕ) := ⟨Modulus.toFun⟩

def Modulus.finitePart (𝔪 : Modulus K) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ :=
  fun 𝔭 => 𝔪 (Place.finite 𝔭)

def Modulus.infSupport (𝔪 : Modulus K) : Set (NumberField.InfinitePlace K) :=
  {v | 𝔪 (Place.infinite v) ≠ 0}

lemma Modulus.infSupport_subset_real (𝔪 : Modulus K) :
    ∀ v ∈ 𝔪.infSupport, v.IsReal := by
  intro v hv
  exact (NumberField.InfinitePlace.not_isComplex_iff_isReal).mp
    (fun hc => hv (𝔪.complex_zero v hc))

@[ext]
structure SimpleModulus (K : Type*) [Field K] [NumberField K] where
  finite_part : Ideal (NumberField.RingOfIntegers K)
  infinite_part : Set (NumberField.InfinitePlace K)
  real_places : ∀ v ∈ infinite_part, v.IsReal

def SimpleModulus.trivial : SimpleModulus K where
  finite_part := ⊤
  infinite_part := ∅
  real_places := by simp

def Modulus.finitePartIdeal (𝔪 : @Modulus K _ _) : Ideal (NumberField.RingOfIntegers K) :=
  let S := 𝔪.finite_support.preimage (f := Place.finite)
    (fun a _ b _ hab => by cases hab; rfl)
  S.toFinset.prod (fun 𝔭 => 𝔭.asIdeal ^ 𝔪 (Place.finite 𝔭))

def Modulus.dvd (𝔪 𝔫 : Modulus K) : Prop :=
  ∀ v, 𝔪 v ≤ 𝔫 v

def Modulus.gcd (𝔪 𝔫 : Modulus K) : Modulus K where
  toFun v := min (𝔪 v) (𝔫 v)
  finite_support := by
    apply Set.Finite.subset (𝔪.finite_support.union 𝔫.finite_support)
    intro v hv
    simp only [Set.mem_setOf_eq, Set.mem_union] at *
    by_contra h
    push Not at h
    exact hv (by simp [h.1, h.2])
  inf_le_one := fun v => le_trans (min_le_left _ _) (𝔪.inf_le_one v)
  complex_zero := fun v hv => by simp [𝔪.complex_zero v hv, 𝔫.complex_zero v hv]

def Modulus.lcm (𝔪 𝔫 : Modulus K) : Modulus K where
  toFun v := max (𝔪 v) (𝔫 v)
  finite_support := by
    apply Set.Finite.subset (𝔪.finite_support.union 𝔫.finite_support)
    intro v hv
    simp only [Set.mem_setOf_eq, Set.mem_union] at *
    by_contra h
    push Not at h
    exact hv (by simp [h.1, h.2])
  inf_le_one := fun v => max_le (𝔪.inf_le_one v) (𝔫.inf_le_one v)
  complex_zero := fun v hv => by simp [𝔪.complex_zero v hv, 𝔫.complex_zero v hv]

def Modulus.trivial : Modulus K where
  toFun _ := 0
  finite_support := by simp
  inf_le_one _ := Nat.zero_le _
  complex_zero _ _ := rfl

universe u

abbrev FinitePlace (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

abbrev FracIdeal (K : Type*) [Field K] [NumberField K] :=
  FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K

def HasTrivialValuation (I : (FracIdeal K)ˣ) (v : FinitePlace K) : Prop :=
  ∃ x ∈ (↑I : FracIdeal K), v.valuation K x = 1

def FracIdeal.IsCoprimeTo (I : (FracIdeal K)ˣ) (v : FinitePlace K) : Prop :=
  HasTrivialValuation I v ∧ HasTrivialValuation I⁻¹ v

lemma hasTrivialValuation_one (v : FinitePlace K) :
    HasTrivialValuation (1 : (FracIdeal K)ˣ) v :=
  ⟨1, by rw [Units.val_one]; exact FractionalIdeal.one_mem_one _, Valuation.map_one _⟩

lemma hasTrivialValuation_mul {a b : (FracIdeal K)ˣ} {v : FinitePlace K}
    (ha : HasTrivialValuation a v) (hb : HasTrivialValuation b v) :
    HasTrivialValuation (a * b) v := by
  obtain ⟨x, hx, hvx⟩ := ha
  obtain ⟨y, hy, hvy⟩ := hb
  exact ⟨x * y, by rw [Units.val_mul]; exact FractionalIdeal.mul_mem_mul hx hy,
    by simp [map_mul, hvx, hvy]⟩

def FracIdealsCoprime_subgroup (K : Type*) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Subgroup (FracIdeal K)ˣ where
  carrier := {I | ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → FracIdeal.IsCoprimeTo I v}
  one_mem' := fun v _ =>
    ⟨hasTrivialValuation_one v, by simpa using hasTrivialValuation_one v⟩
  mul_mem' := fun {a b} ha hb v hv =>
    let ⟨ha1, ha2⟩ := ha v hv
    let ⟨hb1, hb2⟩ := hb v hv
    ⟨hasTrivialValuation_mul ha1 hb1,
     by rw [mul_inv_rev]; exact hasTrivialValuation_mul hb2 ha2⟩
  inv_mem' := fun {a} ha v hv =>
    let ⟨h1, h2⟩ := ha v hv
    ⟨h2, by rwa [inv_inv]⟩

def FracIdealsCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Type u :=
  FracIdealsCoprime_subgroup K 𝔪

instance instCommGroupFracIdealsCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : CommGroup (FracIdealsCoprime K 𝔪) :=
  Subgroup.toCommGroup (FracIdealsCoprime_subgroup K 𝔪)

def IsRayGenerator (𝔪 : Modulus K) (I : FracIdealsCoprime K 𝔪) : Prop :=
  ∃ (α : Kˣ),

    (I.val : (FracIdeal K)ˣ).val =
      FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (α : K) ∧

    (∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
      v.valuation K ((α : K) - 1) ≤
        ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ)))) ∧

    (∀ w : NumberField.InfinitePlace K, 𝔪 (Place.infinite w) ≠ 0 →
      0 < (w.embedding (α : K)).re)

def RayGroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Subgroup (FracIdealsCoprime K 𝔪) :=
  Subgroup.closure {I | IsRayGenerator 𝔪 I}

def RayClassGroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Type u :=
  (FracIdealsCoprime K 𝔪) ⧸ (RayGroup K 𝔪)

instance (𝔪 : @Modulus K _ _) : CommGroup (RayClassGroup K 𝔪) :=
  QuotientGroup.Quotient.commGroup _

noncomputable def choosePrimeOver (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : FinitePlace K) : Ideal (NumberField.RingOfIntegers L) :=
  (Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) 𝔭.asIdeal ⊥ (by simp)).choose

instance choosePrimeOver_isPrime (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : FinitePlace K) :
    (choosePrimeOver K L 𝔭).IsPrime :=
  (Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) 𝔭.asIdeal ⊥ (by simp)).choose_spec.2.1

lemma choosePrimeOver_over (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : FinitePlace K) :
    (choosePrimeOver K L 𝔭).comap
      (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) = 𝔭.asIdeal :=
  (Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) 𝔭.asIdeal ⊥ (by simp)).choose_spec.2.2

lemma choosePrimeOver_ne_bot (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : FinitePlace K) :
    choosePrimeOver K L 𝔭 ≠ ⊥ := by
  intro h
  have hcomap := choosePrimeOver_over K L 𝔭
  rw [h, Ideal.comap_bot_of_injective] at hcomap
  · exact 𝔭.ne_bot hcomap.symm
  · exact FaithfulSMul.algebraMap_injective _ _

instance choosePrimeOver_finite (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : FinitePlace K) :
    Finite (NumberField.RingOfIntegers L ⧸ choosePrimeOver K L 𝔭) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (choosePrimeOver_ne_bot K L 𝔭)

noncomputable def FrobeniusAutomorphism (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : FinitePlace K) : (L ≃ₐ[K] L) :=
  arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) (choosePrimeOver K L 𝔭)

noncomputable def primeAsUnitFracIdeal (K : Type u) [Field K] [NumberField K]
    (𝔭 : FinitePlace K) : (FracIdeal K)ˣ :=
  haveI : IsUnit (𝔭.asIdeal : FracIdeal K) :=
    isUnit_iff_exists_inv.mpr ⟨_, FractionalIdeal.coe_ideal_mul_inv 𝔭.asIdeal 𝔭.ne_bot⟩
  this.unit

theorem primeAsUnitFracIdeal_coprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝔭 : FinitePlace K) (h𝔭 : 𝔪 (Place.finite 𝔭) = 0) :
    (primeAsUnitFracIdeal K 𝔭 : (FracIdeal K)ˣ) ∈ FracIdealsCoprime_subgroup K 𝔪 := by
  intro v hv

  have hne : 𝔭 ≠ v := by intro heq; rw [heq] at h𝔭; exact hv h𝔭

  have hnotsubset : ¬ (𝔭.asIdeal ≤ v.asIdeal) := by
    intro h
    exact hne (IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
      (𝔭.isMaximal.eq_of_le v.isPrime.ne_top h))

  obtain ⟨r, hr𝔭, hrv⟩ := Set.not_subset.mp hnotsubset

  have hval : (primeAsUnitFracIdeal K 𝔭 : FracIdeal K) = 𝔭.asIdeal := by
    simp [primeAsUnitFracIdeal, IsUnit.unit]
  constructor
  ·

    refine ⟨algebraMap _ K r, ?_, ?_⟩
    · rw [hval]
      exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨r, hr𝔭, rfl⟩
    · rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v r).mpr hrv
  ·

    unfold HasTrivialValuation
    simp only [Units.val_inv_eq_inv_val]
    refine ⟨1, ?_, Valuation.map_one _⟩
    rw [hval]
    have hne_zero : (𝔭.asIdeal : FracIdeal K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr 𝔭.ne_bot
    have hinv : 1⁻¹ ≤ (𝔭.asIdeal : FracIdeal K)⁻¹ :=
      FractionalIdeal.inv_anti_mono hne_zero one_ne_zero FractionalIdeal.coeIdeal_le_one
    simp only [inv_one] at hinv
    exact hinv (FractionalIdeal.one_mem_one _)

noncomputable def primeCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝔭 : FinitePlace K) (h𝔭 : 𝔪 (Place.finite 𝔭) = 0) :
    FracIdealsCoprime K 𝔪 :=
  ⟨primeAsUnitFracIdeal K 𝔭, primeAsUnitFracIdeal_coprime K 𝔪 𝔭 h𝔭⟩

def primesCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Set (FracIdealsCoprime K 𝔪) :=
  {I | ∃ (𝔭 : FinitePlace K) (h𝔭 : 𝔪 (Place.finite 𝔭) = 0), I = primeCoprime K 𝔪 𝔭 h𝔭}

set_option maxHeartbeats 800000 in
lemma count_spanSingleton_eq_zero (K : Type u) [Field K] [NumberField K]
    (v : FinitePlace K) (x : K) (hx : x ≠ 0) (hv : v.valuation K x = 1) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) x) = 0 := by
  set R := NumberField.RingOfIntegers K
  obtain ⟨⟨r, ⟨s, hs⟩⟩, hrsx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hs_ne : (s : R) ≠ 0 := nonZeroDivisors.ne_zero hs
  have halgs_ne : algebraMap R K s ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) hs
  have hx_eq : x = algebraMap R K r * (algebraMap R K s)⁻¹ := by
    have h1 := hrsx
    simp only at h1
    field_simp
    linear_combination h1
  have hr_ne : r ≠ 0 := by intro hr; exact hx (by rw [hx_eq, hr, map_zero, zero_mul])
  have hne : FractionalIdeal.spanSingleton (nonZeroDivisors R) x ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
  rw [FractionalIdeal.count_well_defined K v hne (by
    rw [hx_eq, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
        ← FractionalIdeal.coeIdeal_span_singleton]; ring)]
  simp only [sub_eq_zero]
  have hval_eq : v.intValuation r = v.intValuation s := by
    have : v.valuation K x = v.intValuation r * (v.intValuation s)⁻¹ := by
      rw [hx_eq, map_mul, map_inv₀,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    rw [this] at hv
    rwa [mul_inv_eq_one₀ (v.intValuation_ne_zero s hs_ne)] at hv
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_apply,
      IsDedekindDomain.HeightOneSpectrum.intValuation_apply] at hval_eq
  simp only [IsDedekindDomain.HeightOneSpectrum.intValuationDef,
             if_neg hr_ne, if_neg hs_ne] at hval_eq
  exact_mod_cast neg_injective (WithZero.exp_injective hval_eq)

set_option maxHeartbeats 800000 in
lemma count_eq_zero_of_isCoprimeTo (K : Type u) [Field K] [NumberField K]
    (I : (FracIdeal K)ˣ) (v : FinitePlace K)
    (h : FracIdeal.IsCoprimeTo I v) :
    FractionalIdeal.count K v (I : FracIdeal K) = 0 := by
  obtain ⟨⟨x, hx_mem, hx_val⟩, ⟨y, hy_mem, hy_val⟩⟩ := h
  have hx_ne : x ≠ 0 := by intro h0; simp [h0] at hx_val
  have hy_ne : y ≠ 0 := by intro h0; simp [h0] at hy_val
  have h1 : FractionalIdeal.count K v I.val ≤ 0 :=
    calc FractionalIdeal.count K v I.val
        ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ x) :=
          FractionalIdeal.count_mono K v
            (by rwa [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff])
            (FractionalIdeal.spanSingleton_le_iff_mem.mpr hx_mem)
      _ = 0 := count_spanSingleton_eq_zero K v x hx_ne hx_val
  have h2 : 0 ≤ FractionalIdeal.count K v I.val := by
    have hcnt_inv : FractionalIdeal.count K v (I⁻¹ : (FracIdeal K)ˣ).val ≤ 0 :=
      calc FractionalIdeal.count K v (I⁻¹ : (FracIdeal K)ˣ).val
          ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ y) :=
            FractionalIdeal.count_mono K v
              (by rwa [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff])
              (FractionalIdeal.spanSingleton_le_iff_mem.mpr hy_mem)
        _ = 0 := count_spanSingleton_eq_zero K v y hy_ne hy_val
    rw [show (I⁻¹ : (FracIdeal K)ˣ).val = I.val⁻¹ from Units.val_inv_eq_inv_val I,
        FractionalIdeal.count_inv] at hcnt_inv
    linarith
  linarith

theorem primeCoprime_val (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝔭 : FinitePlace K) (h𝔭 : 𝔪 (Place.finite 𝔭) = 0) :
    (primeCoprime K 𝔪 𝔭 h𝔭).val = primeAsUnitFracIdeal K 𝔭 := rfl

theorem primeAsUnitFracIdeal_val (K : Type u) [Field K] [NumberField K]
    (𝔭 : FinitePlace K) :
    (primeAsUnitFracIdeal K 𝔭 : FracIdeal K) = 𝔭.asIdeal := by
  simp [primeAsUnitFracIdeal, IsUnit.unit]

theorem fracIdealsCoprime_closure_primes (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    Subgroup.closure (primesCoprime K 𝔪) = ⊤ := by
  rw [eq_top_iff]
  intro ⟨I, hI⟩ _

  set f : FinitePlace K →₀ ℤ := Multiplicative.toAdd (fractionalIdeal_mulEquiv_finsupp K I) with hf_def

  have hsupp : ∀ v ∈ f.support, 𝔪 (Place.finite v) = 0 := by
    intro v hv
    by_contra hmv
    have : f v = 0 := by
      rw [hf_def, fractionalIdeal_mulEquiv_finsupp_apply]
      exact count_eq_zero_of_isCoprimeTo K I v (hI v hmv)
    exact (Finsupp.mem_support_iff.mp hv) this

  set S := Subgroup.closure (primesCoprime K 𝔪)


  suffices h : ⟨I, hI⟩ = f.support.attach.prod (fun ⟨v, hv⟩ =>
      (primeCoprime K 𝔪 v (hsupp v hv)) ^ (f v)) by
    rw [h]
    exact S.prod_mem (fun ⟨v, hv⟩ _ =>
      S.zpow_mem (Subgroup.subset_closure ⟨v, hsupp v hv, rfl⟩) (f v))

  have hI_eq : I = (fractionalIdeal_mulEquiv_finsupp K).symm (Multiplicative.ofAdd f) := by
    rw [hf_def]; simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply]


  have hprod_units : I = ∏ v ∈ f.support, primeAsUnitFracIdeal K v ^ f v := by
    rw [hI_eq]
    ext
    rw [fractionalIdeal_mulEquiv_finsupp_symm_apply]
    simp only [Finsupp.prod, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      primeAsUnitFracIdeal_val]

  apply Subtype.ext

  change I = (FracIdealsCoprime_subgroup K 𝔪).subtype
    (∏ x ∈ f.support.attach, (fun ⟨v, hv⟩ => (primeCoprime K 𝔪 v (hsupp v hv)) ^ (f v)) x)
  rw [map_prod]

  simp only [Subgroup.coe_subtype]

  exact hprod_units.trans (Finset.prod_attach _ _).symm

abbrev CoprimePrimes (K : Type u) [Field K] [NumberField K] (𝔪 : Modulus K) :=
  {𝔭 : FinitePlace K // 𝔪 (Place.finite 𝔭) = 0}

noncomputable def freeGroupToCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    FreeGroup (CoprimePrimes K 𝔪) →* FracIdealsCoprime K 𝔪 :=
  FreeGroup.lift (fun p => primeCoprime K 𝔪 p.1 p.2)

noncomputable def freeGroupToGal (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔪 : Modulus K) :
    FreeGroup (CoprimePrimes K 𝔪) →* (L ≃ₐ[K] L) :=
  FreeGroup.lift (fun p => FrobeniusAutomorphism K L p.1)

theorem primesCoprime_eq_range (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    primesCoprime K 𝔪 =
      Set.range (fun (p : CoprimePrimes K 𝔪) => primeCoprime K 𝔪 p.1 p.2) := by
  ext I
  simp only [primesCoprime, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨𝔭, h𝔭, rfl⟩
    exact ⟨⟨𝔭, h𝔭⟩, rfl⟩
  · rintro ⟨⟨𝔭, h𝔭⟩, rfl⟩
    exact ⟨𝔭, h𝔭, rfl⟩

theorem freeGroupToCoprime_surjective (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    Function.Surjective (freeGroupToCoprime K 𝔪) := by
  rw [← MonoidHom.range_eq_top]
  rw [show freeGroupToCoprime K 𝔪 = FreeGroup.lift
    (fun p => primeCoprime K 𝔪 p.1 p.2) from rfl]
  rw [FreeGroup.range_lift_eq_closure]
  rw [← primesCoprime_eq_range]
  exact fracIdealsCoprime_closure_primes K 𝔪

theorem fractionalIdeal_mulEquiv_finsupp_primeAsUnit (K : Type u) [Field K] [NumberField K]
    (p : FinitePlace K) :
    fractionalIdeal_mulEquiv_finsupp K (primeAsUnitFracIdeal K p) =
      Multiplicative.ofAdd (Finsupp.single p 1) := by
  rw [← ofAdd_toAdd (fractionalIdeal_mulEquiv_finsupp K (primeAsUnitFracIdeal K p))]
  congr 1
  ext v
  classical
  rw [fractionalIdeal_mulEquiv_finsupp_apply, Finsupp.single_apply, primeAsUnitFracIdeal_val]
  by_cases h : p = v
  · rw [if_pos h, h]; exact FractionalIdeal.count_self K v
  · rw [if_neg h]; exact FractionalIdeal.count_maximal_coprime K v h

theorem freeGroupToCoprime_ker_le_commutator (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    (freeGroupToCoprime K 𝔪).ker ≤ commutator (FreeGroup (CoprimePrimes K 𝔪)) := by


  set α := CoprimePrimes K 𝔪


  let r : FracIdealsCoprime K 𝔪 →* Abelianization (FreeGroup α) :=
    { toFun := fun I =>
        let exps := Multiplicative.toAdd (fractionalIdeal_mulEquiv_finsupp K I.val)

        let exps_restricted : α →₀ ℤ :=
          Finsupp.comapDomain Subtype.val exps (Subtype.val_injective.injOn)

        Additive.toMul (Finsupp.toFreeAbelianGroup exps_restricted)
      map_one' := by
        dsimp only
        conv_lhs => rw [show (1 : FracIdealsCoprime K 𝔪).val = 1 from rfl]
        rw [map_one, toAdd_one, Finsupp.comapDomain_zero, map_zero]
        exact toMul_zero
      map_mul' := fun a b => by
        dsimp only
        conv_lhs => rw [show (a * b : FracIdealsCoprime K 𝔪).val = a.val * b.val from rfl]
        rw [map_mul, toAdd_mul, Finsupp.comapDomain_add, map_add]
        exact toMul_add _ _ }


  have hretract : r.comp (freeGroupToCoprime K 𝔪) = Abelianization.of := by


    ext p


    simp only [MonoidHom.comp_apply, freeGroupToCoprime, FreeGroup.lift_apply_of]


    change (fun I =>
      let exps := Multiplicative.toAdd (fractionalIdeal_mulEquiv_finsupp K I.val)
      let exps_restricted : α →₀ ℤ :=
        Finsupp.comapDomain Subtype.val exps (Subtype.val_injective.injOn)
      Additive.toMul (Finsupp.toFreeAbelianGroup exps_restricted))
      (primeCoprime K 𝔪 p.1 p.2) = _

    simp only [primeCoprime_val, fractionalIdeal_mulEquiv_finsupp_primeAsUnit, toAdd_ofAdd]

    rw [Finsupp.comapDomain_single]

    simp [Finsupp.toFreeAbelianGroup]

    rfl

  intro x hx
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  rw [MonoidHom.mem_ker] at hx
  have := congr_fun (congr_arg DFunLike.coe hretract) x
  simp only [MonoidHom.comp_apply] at this
  rw [hx, map_one] at this
  exact this.symm

theorem artinMap_ker_condition (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [KroneckerWeber.IsAbelianExtension K L]
    (𝔪 : Modulus K) :
    (freeGroupToCoprime K 𝔪).ker ≤ (freeGroupToGal K L 𝔪).ker := by
  haveI : IsGalois K L := KroneckerWeber.IsAbelianExtension.isGalois


  letI galCommGroup : CommGroup (L ≃ₐ[K] L) :=
    { (inferInstance : Group (L ≃ₐ[K] L)) with
      mul_comm := KroneckerWeber.IsAbelianExtension.comm }


  have hcomm_gal : commutator (FreeGroup (CoprimePrimes K 𝔪)) ≤ (freeGroupToGal K L 𝔪).ker :=
    Abelianization.commutator_subset_ker _


  have hker_le_comm : (freeGroupToCoprime K 𝔪).ker ≤ commutator (FreeGroup (CoprimePrimes K 𝔪)) :=
    freeGroupToCoprime_ker_le_commutator K 𝔪
  exact le_trans hker_le_comm hcomm_gal

theorem artinMapExists (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [KroneckerWeber.IsAbelianExtension K L]
    (𝔪 : Modulus K) :
    ∃ (ψ : FracIdealsCoprime K 𝔪 →* (L ≃ₐ[K] L)),
      ∀ (𝔭 : FinitePlace K) (h𝔭 : 𝔪 (Place.finite 𝔭) = 0),
        ψ (primeCoprime K 𝔪 𝔭 h𝔭) = FrobeniusAutomorphism K L 𝔭 := by

  let ψ := (MonoidHom.liftOfSurjective (freeGroupToCoprime K 𝔪)
    (freeGroupToCoprime_surjective K 𝔪))
    ⟨freeGroupToGal K L 𝔪, artinMap_ker_condition K L 𝔪⟩
  refine ⟨ψ, fun 𝔭 h𝔭 => ?_⟩


  show ψ ((fun (p : CoprimePrimes K 𝔪) => primeCoprime K 𝔪 p.1 p.2) ⟨𝔭, h𝔭⟩) = FrobeniusAutomorphism K L 𝔭

  have h1 : (fun p => primeCoprime K 𝔪 p.1 p.2) (⟨𝔭, h𝔭⟩ : CoprimePrimes K 𝔪) =
    freeGroupToCoprime K 𝔪 (FreeGroup.of ⟨𝔭, h𝔭⟩) := by
    simp [freeGroupToCoprime]
  rw [h1]
  simp only [ψ, MonoidHom.liftOfRightInverse_comp_apply]
  simp [freeGroupToGal]

noncomputable def ArtinMap (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [KroneckerWeber.IsAbelianExtension K L]
    (𝔪 : Modulus K) :
    FracIdealsCoprime K 𝔪 →* (L ≃ₐ[K] L) :=
  (artinMapExists K L 𝔪).choose

theorem artinMap_at_prime_eq_frobenius
    (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [KroneckerWeber.IsAbelianExtension K L]
    (𝔪 : Modulus K) (𝔭 : FinitePlace K) (h𝔭 : 𝔪 (Place.finite 𝔭) = 0) :
    ArtinMap K L 𝔪 (primeCoprime K 𝔪 𝔭 h𝔭) = FrobeniusAutomorphism K L 𝔭 :=
  (artinMapExists K L 𝔪).choose_spec 𝔭 h𝔭

structure IsRayClassField (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [KroneckerWeber.IsAbelianExtension K L]
    (𝔪 : Modulus K) : Prop where
  finiteDimensional : FiniteDimensional K L
  unramified_outside :
    ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔪 (Place.finite 𝔭) = 0 →
      ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
        𝔔.LiesOver 𝔭.asIdeal →
        Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) 𝔔
  kernel_eq_ray_group :
    MonoidHom.ker (ArtinMap K L 𝔪) = RayGroup K 𝔪

lemma restrictNormalHom_isArithFrobAt
    (K : Type u) (L : Type u) (M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsGalois K L] [IsGalois K M]
    [IsScalarTower K L M]
    (Q_M : Ideal (NumberField.RingOfIntegers M))
    [Q_M.IsPrime] [Finite (NumberField.RingOfIntegers M ⧸ Q_M)]
    (σ : M ≃ₐ[K] M) (hσ : IsArithFrobAt (NumberField.RingOfIntegers K) σ Q_M) :
    IsArithFrobAt (NumberField.RingOfIntegers K) (AlgEquiv.restrictNormalHom L σ)
      (Q_M.comap (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))) := by
  intro y
  rw [Ideal.mem_comap, map_sub, map_pow]

  have hunder : (Q_M.comap (algebraMap (NumberField.RingOfIntegers L)
      (NumberField.RingOfIntegers M))).under (NumberField.RingOfIntegers K)
      = Q_M.under (NumberField.RingOfIntegers K) := by
    simp only [Ideal.under_def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  rw [hunder]

  have compat : (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))
      ((MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)
        (AlgEquiv.restrictNormalHom L σ)) y) =
      (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers M) σ)
        (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M) y) := by
    ext
    exact AlgEquiv.restrictNormal_commutes σ L ↑y
  rw [compat]

  exact hσ (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M) y)

lemma choosePrimeOver_comap_ne_bot
    (K : Type u) (L : Type u) (M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsGalois K L] [IsGalois K M]
    [IsScalarTower K L M]
    (𝔭 : FinitePlace K) :
    (choosePrimeOver K M 𝔭).comap
      (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M)) ≠ ⊥ := by
  intro h
  have hunder := choosePrimeOver_over K M 𝔭
  have : ((choosePrimeOver K M 𝔭).comap
      (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))).comap
      (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) = 𝔭.asIdeal := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]; exact hunder
  rw [h, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)] at this
  exact 𝔭.ne_bot this.symm

instance choosePrimeOver_comap_isPrime
    (K : Type u) (L : Type u) (M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsGalois K L] [IsGalois K M]
    [IsScalarTower K L M]
    (𝔭 : FinitePlace K) :
    ((choosePrimeOver K M 𝔭).comap
      (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))).IsPrime :=
  Ideal.IsPrime.comap _

instance choosePrimeOver_comap_finite
    (K : Type u) (L : Type u) (M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsGalois K L] [IsGalois K M]
    [IsScalarTower K L M]
    (𝔭 : FinitePlace K) :
    Finite (NumberField.RingOfIntegers L ⧸
      (choosePrimeOver K M 𝔭).comap
        (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (choosePrimeOver_comap_ne_bot K L M 𝔭)

noncomputable instance galAutFaithfulSMulRingOfIntegers
    (K : Type u) (L : Type u)
    [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    FaithfulSMul (L ≃ₐ[K] L) (NumberField.RingOfIntegers L) where
  eq_of_smul_eq_smul {σ τ} h := by
    have key : ∀ (a : NumberField.RingOfIntegers L),
        (σ : L ≃ₐ[K] L) a.val = (τ : L ≃ₐ[K] L) a.val :=
      fun a => congrArg Subtype.val (h a)
    ext x
    obtain ⟨⟨a, ⟨b, hb⟩⟩, hx⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers L)) x
    simp only at hx
    have hx' : x * (b : L) = (a : L) := by convert hx using 1 <;> rfl
    have : σ x * σ (b : L) = τ x * τ (b : L) := by
      calc σ x * σ (b : L) = σ (x * (b : L)) := (map_mul σ x (b : L)).symm
        _ = σ (a : L) := by rw [hx']
        _ = τ (a : L) := key a
        _ = τ (x * (b : L)) := by rw [hx']
        _ = τ x * τ (b : L) := map_mul τ x (b : L)
    rw [key b] at this
    have hb_ne : (τ : L ≃ₐ[K] L) (b : L) ≠ 0 := by
      intro h0
      have : (b : L) = 0 := by
        rw [show (b : L) = τ.symm (τ (b : L)) from (τ.symm_apply_apply _).symm, h0, map_zero]
      have hb' := map_ne_zero_of_mem_nonZeroDivisors
        (algebraMap (NumberField.RingOfIntegers L) L) (IsFractionRing.injective _ _) hb
      rw [NumberField.RingOfIntegers.coe_eq_algebraMap] at this
      exact hb' this
    exact mul_right_cancel₀ hb_ne this

lemma choosePrimeOver_comap_over
    (K : Type u) (L : Type u) (M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsGalois K L] [IsGalois K M]
    [IsScalarTower K L M]
    (𝔭 : FinitePlace K) :
    ((choosePrimeOver K M 𝔭).comap
        (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))).comap
      (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) = 𝔭.asIdeal := by
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, choosePrimeOver_over]

theorem prop_7_13_restrictNormalHom_arithFrobAt
    (K : Type u) (L : Type u) (M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsGalois K L] [IsGalois K M]
    [IsScalarTower K L M]
    (𝔭 : FinitePlace K)
    [Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K)
      ((choosePrimeOver K M 𝔭).comap
        (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M)))] :
    (AlgEquiv.restrictNormalHom L)
      (arithFrobAt (NumberField.RingOfIntegers K) (M ≃ₐ[K] M) (choosePrimeOver K M 𝔭)) =
    arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L)
      ((choosePrimeOver K M 𝔭).comap
        (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))) := by

  set Q_M := choosePrimeOver K M 𝔭
  set Q_L := Q_M.comap (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))

  have h_lhs : IsArithFrobAt (NumberField.RingOfIntegers K)
      ((AlgEquiv.restrictNormalHom L)
        (arithFrobAt (NumberField.RingOfIntegers K) (M ≃ₐ[K] M) Q_M)) Q_L :=
    restrictNormalHom_isArithFrobAt K L M Q_M
      (arithFrobAt (NumberField.RingOfIntegers K) (M ≃ₐ[K] M) Q_M)
      (IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers K) (M ≃ₐ[K] M) Q_M)
  have h_rhs : IsArithFrobAt (NumberField.RingOfIntegers K)
      (arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q_L) Q_L :=
    IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q_L

  have hQ : Q_L.primeCompl ≤ nonZeroDivisors (NumberField.RingOfIntegers L) :=
    Ideal.primeCompl_le_nonZeroDivisors Q_L
  exact MulSemiringAction.toAlgHom_injective
    (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)
    (h_lhs.eq_of_isUnramifiedAt h_rhs hQ)

lemma arithFrobAt_eq_of_under_eq
    (K : Type u) (L : Type u)
    [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L]
    [KroneckerWeber.IsAbelianExtension K L]
    (Q Q' : Ideal (NumberField.RingOfIntegers L))
    [Q.IsPrime] [Finite (NumberField.RingOfIntegers L ⧸ Q)]
    [Q'.IsPrime] [Finite (NumberField.RingOfIntegers L ⧸ Q')]
    (h : Q.under (NumberField.RingOfIntegers K) = Q'.under (NumberField.RingOfIntegers K)) :
    arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q =
    arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q' := by
  have hconj := isConj_arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q Q' h
  exact hconj.eq_of_left_mem_center
    (Semigroup.mem_center_iff.mpr (fun x =>
      (KroneckerWeber.IsAbelianExtension.comm _ x).symm))

theorem restrictNormalHom_frobeniusAutomorphism
    (K : Type u) (L : Type u) (M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsGalois K L] [IsGalois K M]
    [IsScalarTower K L M]
    [KroneckerWeber.IsAbelianExtension K L]
    (𝔭 : FinitePlace K)
    [Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K)
      ((choosePrimeOver K M 𝔭).comap
        (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M)))] :
    (AlgEquiv.restrictNormalHom L) (FrobeniusAutomorphism K M 𝔭) = FrobeniusAutomorphism K L 𝔭 := by

  unfold FrobeniusAutomorphism


  rw [prop_7_13_restrictNormalHom_arithFrobAt K L M 𝔭]


  exact arithFrobAt_eq_of_under_eq K L _ _ (by
    simp only [Ideal.under_def]
    rw [choosePrimeOver_comap_over K L M 𝔭, choosePrimeOver_over K L 𝔭])

theorem prop_7_22_artinMap_at_prime
    (K : Type u) (L : Type u) (M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [KroneckerWeber.IsAbelianExtension K L] [KroneckerWeber.IsAbelianExtension K M]
    [IsScalarTower K L M]
    (𝔪 : Modulus K)
    (𝔭 : FinitePlace K) (h𝔭 : 𝔪 (Place.finite 𝔭) = 0)
    [Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K)
      ((choosePrimeOver K M 𝔭).comap
        (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M)))] :
    (AlgEquiv.restrictNormalHom L) (ArtinMap K M 𝔪 (primeCoprime K 𝔪 𝔭 h𝔭)) =
      ArtinMap K L 𝔪 (primeCoprime K 𝔪 𝔭 h𝔭) := by
  rw [artinMap_at_prime_eq_frobenius K M 𝔪 𝔭 h𝔭,
      artinMap_at_prime_eq_frobenius K L 𝔪 𝔭 h𝔭]
  exact restrictNormalHom_frobeniusAutomorphism K L M 𝔭

theorem proposition_21_1_artin_commutes
    (K : Type u) (L : Type u) (M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [KroneckerWeber.IsAbelianExtension K L] [KroneckerWeber.IsAbelianExtension K M]
    [IsScalarTower K L M]
    (𝔪 : Modulus K)
    (hdiv : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      𝔪 (Place.finite 𝔭) = 0 →
      ∀ (𝔔 : Ideal (𝓞 L)) [𝔔.IsPrime],
        𝔔.LiesOver 𝔭.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 K) 𝔔)
    (I : FracIdealsCoprime K 𝔪) :
    (AlgEquiv.restrictNormalHom L) (ArtinMap K M 𝔪 I) = ArtinMap K L 𝔪 I := by


  have heq : (AlgEquiv.restrictNormalHom L).comp (ArtinMap K M 𝔪) = ArtinMap K L 𝔪 := by
    apply MonoidHom.eq_of_eqOn_dense (fracIdealsCoprime_closure_primes K 𝔪)

    intro x hx
    obtain ⟨𝔭, h𝔭, rfl⟩ := hx

    haveI : Algebra.IsUnramifiedAt (𝓞 K)
      ((choosePrimeOver K M 𝔭).comap (algebraMap (𝓞 L) (𝓞 M))) :=
      hdiv 𝔭 h𝔭 _ (Ideal.LiesOver.mk ((choosePrimeOver_comap_over K L M 𝔭).symm ▸
        (Ideal.under_def (𝓞 K) _).symm))
    exact prop_7_22_artinMap_at_prime K L M 𝔪 𝔭 h𝔭
  exact DFunLike.congr_fun heq I

def Modulus.infSupportFinset (𝔪 : @Modulus K _ _) :
    Finset (NumberField.InfinitePlace K) :=
  (𝔪.finite_support.preimage (f := Place.infinite)
    (fun a _ b _ hab => by cases hab; rfl)).toFinset

def UnitsCoprime_subgroup' (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Subgroup Kˣ where
  carrier := {α | ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
    v.valuation K (α : K) = 1}
  one_mem' := fun v _ => Valuation.map_one _
  mul_mem' := fun {a b} ha hb v hv => by simp [map_mul, ha v hv, hb v hv]
  inv_mem' := fun {a} ha v hv => by simp [map_inv₀, ha v hv]

def UnitsCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Type u :=
  UnitsCoprime_subgroup' K 𝔪

omit [NumberField K] in
lemma embedding_im_zero {w : NumberField.InfinitePlace K} (hw : w.IsReal) (x : K) :
    (w.embedding x).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  exact RingHom.congr_fun
    (NumberField.ComplexEmbedding.isReal_iff.mp (NumberField.InfinitePlace.isReal_iff.mp hw)) x

def UnitsCongruent_subgroup' (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Subgroup Kˣ where
  carrier := {α |

    (∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
      v.valuation K (α : K) = 1) ∧

    (∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
      v.valuation K ((α : K) - 1) ≤
        ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ)))) ∧

    (∀ w : NumberField.InfinitePlace K, 𝔪 (Place.infinite w) ≠ 0 →
      0 < (w.embedding (α : K)).re)}
  one_mem' := by
    refine ⟨fun v _ => Valuation.map_one _, fun v _ => ?_, fun w _ => ?_⟩
    · simp only [Units.val_one, sub_self, map_zero]
      exact WithZero.zero_le _
    · simp [map_one, Complex.one_re]
  mul_mem' := by
    intro a b ⟨ha_cop, ha_cong, ha_sign⟩ ⟨hb_cop, hb_cong, hb_sign⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      simp [map_mul, ha_cop v hv, hb_cop v hv]
    · intro v hv
      have key : ((a * b : Kˣ) : K) - 1 = (a : K) * ((b : K) - 1) + ((a : K) - 1) := by
        simp only [Units.val_mul]; ring
      rw [key]
      calc v.valuation K ((a : K) * ((b : K) - 1) + ((a : K) - 1))
          ≤ max (v.valuation K ((a : K) * ((b : K) - 1))) (v.valuation K ((a : K) - 1)) :=
            Valuation.map_add _ _ _
        _ ≤ max (↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ))))
              (↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ)))) := by
            apply max_le_max
            · rw [map_mul, ha_cop v hv, one_mul]; exact hb_cong v hv
            · exact ha_cong v hv
        _ = _ := max_self _
    · intro w hw
      have hw_real : w.IsReal := by
        by_contra h
        exact hw (𝔪.complex_zero w (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp h))
      rw [Units.val_mul, map_mul, Complex.mul_re]
      rw [embedding_im_zero hw_real, embedding_im_zero hw_real]
      simp only [mul_zero, sub_zero]
      exact mul_pos (ha_sign w hw) (hb_sign w hw)
  inv_mem' := by
    intro a ⟨ha_cop, ha_cong, ha_sign⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      simp [map_inv₀, ha_cop v hv]
    · intro v hv
      have key : ((a⁻¹ : Kˣ) : K) - 1 = -((a : K) - 1) * ((a⁻¹ : Kˣ) : K) := by
        simp only [Units.val_inv_eq_inv_val]; field_simp; ring
      rw [key, map_mul, Valuation.map_neg]
      have : v.valuation K ((a⁻¹ : Kˣ) : K) = 1 := by
        rw [Units.val_inv_eq_inv_val, map_inv₀, ha_cop v hv, inv_one]
      rw [this, mul_one]
      exact ha_cong v hv
    · intro w hw
      have hw_real : w.IsReal := by
        by_contra h
        exact hw (𝔪.complex_zero w (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp h))
      rw [Units.val_inv_eq_inv_val, map_inv₀, Complex.inv_re]
      have him : (w.embedding (a : K)).im = 0 := embedding_im_zero hw_real _
      have hnsq : Complex.normSq (w.embedding (a : K)) = (w.embedding (a : K)).re ^ 2 := by
        rw [Complex.normSq_apply, him, mul_zero, add_zero, sq]
      rw [hnsq]
      exact div_pos (ha_sign w hw) (sq_pos_of_pos (ha_sign w hw))

def UnitsCongruent (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Type u :=
  UnitsCongruent_subgroup' K 𝔪

def UnitsCongruent_in_UnitsCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Subgroup (UnitsCoprime_subgroup' K 𝔪) :=
  (UnitsCongruent_subgroup' K 𝔪).subgroupOf (UnitsCoprime_subgroup' K 𝔪)

def QuotientUnits (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Type u :=
  (UnitsCoprime_subgroup' K 𝔪) ⧸ (UnitsCongruent_in_UnitsCoprime K 𝔪)

instance instCommGroupQuotientUnits (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : CommGroup (QuotientUnits K 𝔪) :=
  QuotientGroup.Quotient.commGroup _

def UnitsInCongruenceSubgroup_subgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Subgroup (NumberField.RingOfIntegers K)ˣ :=
  (UnitsCongruent_subgroup' K 𝔪).comap
    (Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom)

def UnitsInCongruenceSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Type u :=
  UnitsInCongruenceSubgroup_subgroup K 𝔪

instance instCommGroupUnitsInCongruenceSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : CommGroup (UnitsInCongruenceSubgroup K 𝔪) :=
  Subgroup.toCommGroup _

def SignsTimesUnits (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Type u :=
  (𝔪.infSupportFinset → Multiplicative (ZMod 2)) ×
    (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)ˣ

instance instCommGroupSignsTimesUnits (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : CommGroup (SignsTimesUnits K 𝔪) :=
  Prod.instCommGroup

noncomputable def instFintypeSignsTimesUnits (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Fintype (SignsTimesUnits K 𝔪) := by
  classical
  unfold SignsTimesUnits
  have hne : 𝔪.finitePartIdeal ≠ ⊥ := by
    unfold Modulus.finitePartIdeal
    rw [ne_eq, ← Ideal.zero_eq_bot, ← ne_eq]
    exact Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ => by
      rw [ne_eq, Ideal.zero_eq_bot, ← ne_eq, ← Ideal.zero_eq_bot]
      exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact 𝔭.ne_bot))
  haveI : Finite (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient hne
  haveI : Fintype (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal) := Fintype.ofFinite _
  exact inferInstance

attribute [instance] instFintypeSignsTimesUnits

lemma Modulus.finitePartIdeal_ne_bot (𝔪 : @Modulus K _ _) :
    𝔪.finitePartIdeal ≠ ⊥ := by
  unfold Modulus.finitePartIdeal
  rw [ne_eq, ← Ideal.zero_eq_bot, ← ne_eq]
  exact Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ => by
    rw [ne_eq, Ideal.zero_eq_bot, ← ne_eq, ← Ideal.zero_eq_bot]
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact 𝔭.ne_bot))

theorem lemma_21_7_ideal_class_coprime_rep
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (𝔞 : Ideal A) (c : ClassGroup A) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ (I : nonZeroDivisors (Ideal A)),
      ClassGroup.mk0 I = c
      ∧ (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum A,
        𝔭.asIdeal ∣ 𝔞 → ¬(𝔭.asIdeal ∣ (I : Ideal A))) := by

  obtain ⟨⟨J, hJ_mem⟩, hJ_class⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ_ne : J ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp hJ_mem

  have hle : J * 𝔞 ≤ J := Ideal.mul_le_right
  have hne : J * 𝔞 ≠ ⊥ := mul_ne_zero hJ_ne h𝔞
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
  have ha_le : Ideal.span {a} ≤ J := by rw [← ha]; exact le_sup_right
  obtain ⟨K, hK_eq⟩ := Ideal.dvd_iff_le.mpr ha_le

  have hK_coprime : K ⊔ 𝔞 = ⊤ := by
    rw [sup_comm]
    exact mul_left_cancel₀ hJ_ne
      (by rw [Ideal.mul_sup, Ideal.mul_top, ← hK_eq, ha])
  by_cases hK_ne : K = ⊥
  ·
    have h𝔞_top : 𝔞 = ⊤ := by rw [← hK_coprime, hK_ne, bot_sup_eq]
    obtain ⟨⟨K', hK'_mem⟩, hK'_class⟩ := ClassGroup.mk0_surjective c
    exact ⟨⟨K', hK'_mem⟩, hK'_class, fun 𝔭 h𝔭 _ => by
      rw [h𝔞_top] at h𝔭
      exact 𝔭.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp h𝔭))⟩
  ·
    have hJK_ne : J * K ≠ ⊥ := mul_ne_zero hJ_ne hK_ne

    have h1 : ClassGroup.mk0
        ⟨J * K, mem_nonZeroDivisors_iff_ne_zero.mpr hJK_ne⟩ = 1 := by
      rw [ClassGroup.mk0_eq_one_iff]
      rw [← hK_eq]; exact ⟨⟨a, rfl⟩⟩

    have h2 : ClassGroup.mk0
        ⟨J * K, mem_nonZeroDivisors_iff_ne_zero.mpr hJK_ne⟩ =
      ClassGroup.mk0 ⟨J, hJ_mem⟩ *
        ClassGroup.mk0
          ⟨K, mem_nonZeroDivisors_iff_ne_zero.mpr hK_ne⟩ := by
      rw [← MonoidHom.map_mul]; congr 1
    rw [h2, hJ_class] at h1

    exact ⟨⟨K, mem_nonZeroDivisors_iff_ne_zero.mpr hK_ne⟩,
      (eq_of_inv_mul_eq_one h1).symm,


      fun 𝔭 h𝔭𝔞 h𝔭K => by
        have : K ⊔ 𝔞 ≤ 𝔭.asIdeal :=
          sup_le (Ideal.dvd_iff_le.mp h𝔭K) (Ideal.dvd_iff_le.mp h𝔭𝔞)
        rw [hK_coprime] at this
        exact 𝔭.isPrime.ne_top (top_le_iff.mp this)⟩

def exactSeq_map1 (𝔪 : @Modulus K _ _) :
    UnitsInCongruenceSubgroup K 𝔪 →* (NumberField.RingOfIntegers K)ˣ :=
  (UnitsInCongruenceSubgroup_subgroup K 𝔪).subtype

def okUnitsToKUnits : (NumberField.RingOfIntegers K)ˣ →* Kˣ :=
  Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom

lemma valuation_algebraMap_unit_eq_one
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : (NumberField.RingOfIntegers K)ˣ) :
    v.valuation K (algebraMap (NumberField.RingOfIntegers K) K u.val) = 1 := by
  have h1 : v.valuation K (algebraMap _ K u.val) ≤ 1 := v.valuation_le_one u.val
  have h2 : v.valuation K (algebraMap _ K u.inv) ≤ 1 := v.valuation_le_one u.inv
  have h3 : v.valuation K (algebraMap _ K u.val) *
             v.valuation K (algebraMap _ K u.inv) = 1 := by
    rw [← map_mul (v.valuation K), ← map_mul (algebraMap _ K), u.val_inv, map_one, map_one]
  exact le_antisymm h1 (by
    calc (1 : WithZero (Multiplicative ℤ))
        = v.valuation K (algebraMap _ K u.val) *
          v.valuation K (algebraMap _ K u.inv) := h3.symm
      _ ≤ v.valuation K (algebraMap _ K u.val) * 1 := by gcongr
      _ = v.valuation K (algebraMap _ K u.val) := mul_one _)

theorem okUnitsInUnitsCoprime (𝔪 : @Modulus K _ _)
    (u : (NumberField.RingOfIntegers K)ˣ) :
    okUnitsToKUnits u ∈ UnitsCoprime_subgroup' K 𝔪 := by
  intro v _
  exact valuation_algebraMap_unit_eq_one v u

def okUnitsToUnitsCoprime (𝔪 : @Modulus K _ _) :
    (NumberField.RingOfIntegers K)ˣ →* UnitsCoprime_subgroup' K 𝔪 where
  toFun u := ⟨okUnitsToKUnits u, okUnitsInUnitsCoprime 𝔪 u⟩
  map_one' := by
    ext; simp [okUnitsToKUnits, MonoidHom.map_one]
  map_mul' x y := by
    ext; simp [okUnitsToKUnits, MonoidHom.map_mul]

def exactSeq_map2 (𝔪 : @Modulus K _ _) :
    (NumberField.RingOfIntegers K)ˣ →* QuotientUnits K 𝔪 :=
  (QuotientGroup.mk' (UnitsCongruent_in_UnitsCoprime K 𝔪)).comp
    (okUnitsToUnitsCoprime 𝔪)

lemma toPrincipalIdeal_mem_FracIdealsCoprime (𝔪 : @Modulus K _ _)
    (α : Kˣ) (hα : α ∈ UnitsCoprime_subgroup' K 𝔪) :
    toPrincipalIdeal (NumberField.RingOfIntegers K) K α ∈
      FracIdealsCoprime_subgroup K 𝔪 := by
  intro v hv
  constructor
  ·
    refine ⟨(α : K), ?_, hα v hv⟩
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  ·
    refine ⟨((α⁻¹ : Kˣ) : K), ?_, ?_⟩
    · rw [← MonoidHom.map_inv, coe_toPrincipalIdeal]
      exact FractionalIdeal.mem_spanSingleton_self _ _
    · have := (UnitsCoprime_subgroup' K 𝔪).inv_mem hα v hv
      exact this

noncomputable def principalIdealMap (𝔪 : @Modulus K _ _) :
    UnitsCoprime_subgroup' K 𝔪 →* FracIdealsCoprime K 𝔪 where
  toFun α := ⟨toPrincipalIdeal (NumberField.RingOfIntegers K) K (α : Kˣ),
    toPrincipalIdeal_mem_FracIdealsCoprime 𝔪 (α : Kˣ) α.property⟩
  map_one' := by
    apply Subtype.ext
    show toPrincipalIdeal (NumberField.RingOfIntegers K) K (1 : Kˣ) = 1
    exact map_one _
  map_mul' x y := by
    apply Subtype.ext
    show toPrincipalIdeal _ K ((x : Kˣ) * (y : Kˣ)) =
      toPrincipalIdeal _ K (x : Kˣ) * toPrincipalIdeal _ K (y : Kˣ)
    exact map_mul _ _ _

lemma principalIdealMap_val (𝔪 : @Modulus K _ _)
    (α : UnitsCoprime_subgroup' K 𝔪) :
    ((principalIdealMap 𝔪 α).val : (FracIdeal K)ˣ).val =
      FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) ((α : Kˣ) : K) := by
  show (toPrincipalIdeal (NumberField.RingOfIntegers K) K (α : Kˣ) : FracIdeal K) = _
  exact coe_toPrincipalIdeal _

theorem principalIdealMap_congruent_to_ray (𝔪 : @Modulus K _ _)
    (α : UnitsCoprime_subgroup' K 𝔪)
    (hα : (α : Kˣ) ∈ UnitsCongruent_subgroup' K 𝔪) :
    principalIdealMap 𝔪 α ∈ RayGroup K 𝔪 := by


  apply Subgroup.subset_closure

  show IsRayGenerator 𝔪 (principalIdealMap 𝔪 α)
  refine ⟨(α : Kˣ), ?_, ?_, ?_⟩
  ·
    exact principalIdealMap_val 𝔪 α
  ·
    exact hα.2.1
  ·
    exact hα.2.2

def exactSeq_map3 (𝔪 : @Modulus K _ _) :
    QuotientUnits K 𝔪 →* RayClassGroup K 𝔪 :=
  QuotientGroup.lift (UnitsCongruent_in_UnitsCoprime K 𝔪)
    ((QuotientGroup.mk' (RayGroup K 𝔪)).comp (principalIdealMap 𝔪))
    (fun α hα => by
      simp only [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff _).mpr
        (principalIdealMap_congruent_to_ray 𝔪 α
          (Subgroup.mem_subgroupOf.mp hα)))

noncomputable def exactSeq_map4 (𝔪 : @Modulus K _ _) :
    RayClassGroup K 𝔪 →* ClassGroup (NumberField.RingOfIntegers K) :=
  QuotientGroup.lift (RayGroup K 𝔪)
    (ClassGroup.mk.comp (FracIdealsCoprime_subgroup K 𝔪).subtype)
    (by


      rw [RayGroup, Subgroup.closure_le]
      intro I hI
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
      rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff]
      obtain ⟨α, hα_eq, _, _⟩ := hI
      exact ⟨α, by exact_mod_cast hα_eq⟩)

theorem exactSeq_exact_at_units (𝔪 : @Modulus K _ _) :
    MonoidHom.range (exactSeq_map1 𝔪) = MonoidHom.ker (exactSeq_map2 𝔪) := by
  ext u
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  ·
    rintro ⟨x, rfl⟩
    show (exactSeq_map2 𝔪) ((exactSeq_map1 𝔪) x) = 1
    change ((QuotientGroup.mk' (UnitsCongruent_in_UnitsCoprime K 𝔪)).comp
      (okUnitsToUnitsCoprime 𝔪)) ((UnitsInCongruenceSubgroup_subgroup K 𝔪).subtype x) = 1
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

    rw [UnitsCongruent_in_UnitsCoprime, Subgroup.mem_subgroupOf]

    have hx := x.property
    exact Subgroup.mem_comap.mp hx
  ·
    intro h_ker
    have h_ker' : ((QuotientGroup.mk' (UnitsCongruent_in_UnitsCoprime K 𝔪)).comp
      (okUnitsToUnitsCoprime 𝔪)) u = 1 := h_ker
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h_ker'
    rw [UnitsCongruent_in_UnitsCoprime, Subgroup.mem_subgroupOf] at h_ker'
    refine ⟨⟨u, ?_⟩, rfl⟩
    rw [UnitsInCongruenceSubgroup_subgroup, Subgroup.mem_comap]
    convert h_ker' using 1

lemma toPrincipalIdeal_algebraMap_unit'
    (u : (NumberField.RingOfIntegers K)ˣ) :
    toPrincipalIdeal (NumberField.RingOfIntegers K) K
      (Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom u) = 1 := by
  apply Units.ext
  rw [Units.val_one, coe_toPrincipalIdeal]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [← FractionalIdeal.spanSingleton_one, FractionalIdeal.spanSingleton_eq_spanSingleton]
  exact ⟨u⁻¹, by simp [Units.smul_def, Algebra.smul_def]⟩

lemma principalIdealMap_okUnitsToUnitsCoprime_eq_one'
    (𝔪 : @Modulus K _ _) (u : (NumberField.RingOfIntegers K)ˣ) :
    principalIdealMap 𝔪 (okUnitsToUnitsCoprime 𝔪 u) = 1 := by
  apply Subtype.ext
  exact toPrincipalIdeal_algebraMap_unit' u

lemma toPrincipalIdeal_eq_exists_unit'
    (x y : Kˣ) (h : toPrincipalIdeal (NumberField.RingOfIntegers K) K x =
      toPrincipalIdeal (NumberField.RingOfIntegers K) K y) :
    ∃ u : (NumberField.RingOfIntegers K)ˣ,
      x = Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom u * y := by
  have h1 : toPrincipalIdeal (NumberField.RingOfIntegers K) K (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : (toPrincipalIdeal (NumberField.RingOfIntegers K) K (x * y⁻¹) :
    FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) = 1 := by
    rw [h1]; simp
  rw [coe_toPrincipalIdeal, ← FractionalIdeal.spanSingleton_one,
      FractionalIdeal.spanSingleton_eq_spanSingleton] at h2
  obtain ⟨z, hz⟩ := h2
  refine ⟨z⁻¹, ?_⟩
  have hz_units : Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom z *
      (x * y⁻¹) = 1 := by
    ext
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Units.val_inv_eq_inv_val, Units.val_one]
    rw [Units.smul_def, Algebra.smul_def] at hz
    simp only [Units.val_mul, Units.val_inv_eq_inv_val] at hz
    exact hz
  have hxy : x * y⁻¹ =
      Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom z⁻¹ :=
    mul_left_cancel
      (a := Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom z)
      (by rw [hz_units, ← map_mul]; simp)
  calc x = (x * y⁻¹) * y := by group
    _ = Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom z⁻¹ * y := by rw [hxy]

lemma valuation_eq_one_of_spanSingleton_coprime'
    (v : FinitePlace K) (α : Kˣ)
    (h1 : HasTrivialValuation (toPrincipalIdeal (NumberField.RingOfIntegers K) K α) v)
    (h2 : HasTrivialValuation (toPrincipalIdeal (NumberField.RingOfIntegers K) K α)⁻¹ v) :
    v.valuation K (α : K) = 1 := by

  obtain ⟨x, hx_mem, hx_val⟩ : ∃ x ∈ FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) (α : K),
      v.valuation K x = 1 := by
    rwa [HasTrivialValuation, coe_toPrincipalIdeal] at h1
  obtain ⟨y, hy_mem, hy_val⟩ : ∃ x ∈ FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) ((α⁻¹ : Kˣ) : K),
      v.valuation K x = 1 := by
    have : HasTrivialValuation (toPrincipalIdeal (NumberField.RingOfIntegers K) K α⁻¹) v := by
      rwa [map_inv]
    rwa [HasTrivialValuation, coe_toPrincipalIdeal] at this
  rw [FractionalIdeal.mem_spanSingleton] at hx_mem hy_mem
  obtain ⟨r, hr⟩ := hx_mem
  obtain ⟨s, hs⟩ := hy_mem

  subst hr; subst hs
  simp only [Algebra.smul_def] at hx_val hy_val
  rw [map_mul] at hx_val hy_val
  have hr_le : v.valuation K (algebraMap _ K r) ≤ 1 := v.valuation_le_one r
  have hs_le : v.valuation K (algebraMap _ K s) ≤ 1 := v.valuation_le_one s
  have hαα : v.valuation K (α : K) * v.valuation K ((α⁻¹ : Kˣ) : K) = 1 := by
    rw [← map_mul, show (α : K) * ((α⁻¹ : Kˣ) : K) = 1 from by simp, map_one]
  apply le_antisymm
  · calc v.valuation K (α : K)
        = v.valuation K (α : K) * 1 := (mul_one _).symm
      _ = v.valuation K (α : K) * (v.valuation K (algebraMap _ K s) *
          v.valuation K ((α⁻¹ : Kˣ) : K)) := by rw [hy_val]
      _ = (v.valuation K (α : K) * v.valuation K ((α⁻¹ : Kˣ) : K)) *
          v.valuation K (algebraMap _ K s) := by
            rw [mul_assoc, mul_comm (v.valuation K (algebraMap _ K s))]
      _ = 1 * v.valuation K (algebraMap _ K s) := by rw [hαα]
      _ = v.valuation K (algebraMap _ K s) := one_mul _
      _ ≤ 1 := hs_le
  · calc (1 : WithZero (Multiplicative ℤ))
        = v.valuation K (algebraMap _ K r) * v.valuation K (α : K) := hx_val.symm
      _ ≤ 1 * v.valuation K (α : K) := by gcongr
      _ = v.valuation K (α : K) := one_mul _

lemma rayGroup_le_map_congruent' (𝔪 : @Modulus K _ _) :
    RayGroup K 𝔪 ≤
      Subgroup.map (principalIdealMap 𝔪) (UnitsCongruent_in_UnitsCoprime K 𝔪) := by
  rw [RayGroup, Subgroup.closure_le]
  intro I hI
  obtain ⟨α, hI_eq, hI_cong, hI_sign⟩ := hI


  have hα_coprime : α ∈ UnitsCoprime_subgroup' K 𝔪 := by
    intro v hv
    have hI_cop := I.property v hv


    have hI_val_eq : I.val = toPrincipalIdeal (NumberField.RingOfIntegers K) K α := by
      apply Units.val_injective
      rw [coe_toPrincipalIdeal]
      exact hI_eq
    rw [hI_val_eq] at hI_cop
    exact valuation_eq_one_of_spanSingleton_coprime' v α hI_cop.1 hI_cop.2

  set γ : UnitsCoprime_subgroup' K 𝔪 := ⟨α, hα_coprime⟩

  have hγ_cong : γ ∈ UnitsCongruent_in_UnitsCoprime K 𝔪 := by
    rw [UnitsCongruent_in_UnitsCoprime, Subgroup.mem_subgroupOf]
    exact ⟨hα_coprime, hI_cong, hI_sign⟩

  have hγ_eq : principalIdealMap 𝔪 γ = I := by
    apply Subtype.ext
    apply Units.val_injective
    simp only [principalIdealMap, MonoidHom.coe_mk, OneHom.coe_mk, coe_toPrincipalIdeal]
    exact hI_eq.symm


  exact ⟨γ, hγ_cong, hγ_eq⟩

theorem exactSeq_exact_at_quotient (𝔪 : @Modulus K _ _) :
    MonoidHom.range (exactSeq_map2 𝔪) = MonoidHom.ker (exactSeq_map3 𝔪) := by
  ext ⟨α⟩
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  ·
    rintro ⟨u, hu⟩
    rw [← hu]
    show exactSeq_map3 𝔪 (exactSeq_map2 𝔪 u) = 1
    simp only [exactSeq_map2, exactSeq_map3]
    erw [QuotientGroup.lift_mk']
    show (QuotientGroup.mk' (RayGroup K 𝔪)) (principalIdealMap 𝔪 ((okUnitsToUnitsCoprime 𝔪) u)) = 1
    rw [principalIdealMap_okUnitsToUnitsCoprime_eq_one' 𝔪 u, map_one]
  ·
    intro h


    have h_mem : principalIdealMap 𝔪 α ∈ RayGroup K 𝔪 := by
      rw [← QuotientGroup.eq_one_iff]
      have key : (exactSeq_map3 𝔪)
          (Quot.mk (QuotientGroup.leftRel (UnitsCongruent_in_UnitsCoprime K 𝔪)) α) =
          ((QuotientGroup.mk' (RayGroup K 𝔪)).comp (principalIdealMap 𝔪)) α := by
        simp only [exactSeq_map3]
        erw [QuotientGroup.lift_mk']
      simp only [MonoidHom.comp_apply] at key


      have h1 : (QuotientGroup.mk' (RayGroup K 𝔪)) (principalIdealMap 𝔪 α) = 1 := by
        rw [← key]; exact h
      rwa [QuotientGroup.mk'_apply] at h1

    have hmap := rayGroup_le_map_congruent' 𝔪 h_mem
    rw [Subgroup.mem_map] at hmap
    obtain ⟨β, hβ_cong, hβ_eq⟩ := hmap


    have h_topi : toPrincipalIdeal (NumberField.RingOfIntegers K) K (α : Kˣ) =
        toPrincipalIdeal (NumberField.RingOfIntegers K) K (β : Kˣ) := by
      have := congr_arg Subtype.val hβ_eq
      exact this.symm

    obtain ⟨u, hu⟩ := toPrincipalIdeal_eq_exists_unit' (α : Kˣ) (β : Kˣ) h_topi
    refine ⟨u, ?_⟩

    simp only [exactSeq_map2]
    erw [QuotientGroup.mk'_apply, QuotientGroup.eq]

    rw [UnitsCongruent_in_UnitsCoprime, Subgroup.mem_subgroupOf]


    have hval : (((okUnitsToUnitsCoprime 𝔪 u)⁻¹ * α : ↥(UnitsCoprime_subgroup' K 𝔪)) : Kˣ) =
        (β : Kˣ) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      show (okUnitsToKUnits u)⁻¹ * (α : Kˣ) = (β : Kˣ)
      rw [hu]
      simp [okUnitsToKUnits]
    rw [show (((okUnitsToUnitsCoprime 𝔪 u)⁻¹ * α : ↥(UnitsCoprime_subgroup' K 𝔪)) : Kˣ) =
        (β : Kˣ) from hval]
    exact Subgroup.mem_subgroupOf.mp hβ_cong
theorem exactSeq_exact_at_ray_class (𝔪 : @Modulus K _ _) :
    MonoidHom.range (exactSeq_map3 𝔪) = MonoidHom.ker (exactSeq_map4 𝔪) := by
  ext ⟨I⟩
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  ·
    rintro ⟨⟨α⟩, hα⟩
    rw [← hα]
    show exactSeq_map4 𝔪 (exactSeq_map3 𝔪
      (Quot.mk (QuotientGroup.leftRel (UnitsCongruent_in_UnitsCoprime K 𝔪)) α)) = 1
    have key3 : (exactSeq_map3 𝔪)
        (Quot.mk (QuotientGroup.leftRel (UnitsCongruent_in_UnitsCoprime K 𝔪)) α) =
        ((QuotientGroup.mk' (RayGroup K 𝔪)).comp (principalIdealMap 𝔪)) α := by
      simp only [exactSeq_map3]
      erw [QuotientGroup.lift_mk']
    simp only [MonoidHom.comp_apply] at key3
    rw [key3]
    show (exactSeq_map4 𝔪)
      (QuotientGroup.mk' (RayGroup K 𝔪) (principalIdealMap 𝔪 α)) = 1
    simp only [exactSeq_map4]
    erw [QuotientGroup.lift_mk']
    simp only [MonoidHom.comp_apply]
    rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff]
    refine ⟨((α : Kˣ) : K), ?_⟩

    have := principalIdealMap_val 𝔪 α
    show ((FracIdealsCoprime_subgroup K 𝔪).subtype (principalIdealMap 𝔪 α) : FracIdeal K) = _
    simp only [Subgroup.coe_subtype]
    exact this
  ·
    intro h

    have h_unfold : (ClassGroup.mk (K := K) ((FracIdealsCoprime_subgroup K 𝔪).subtype I)) = 1 := by
      have key4 : (exactSeq_map4 𝔪)
          (Quot.mk (QuotientGroup.leftRel (RayGroup K 𝔪)) I) =
          (ClassGroup.mk.comp (FracIdealsCoprime_subgroup K 𝔪).subtype) I := by
        simp only [exactSeq_map4]
        erw [QuotientGroup.lift_mk']
      simp only [MonoidHom.comp_apply] at key4
      rw [← key4]; exact h

    rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at h_unfold
    obtain ⟨a, ha⟩ := h_unfold


    have ha_ne : a ≠ 0 := by
      intro ha_zero
      rw [ha_zero, FractionalIdeal.spanSingleton_zero] at ha
      simp only [Subgroup.coe_subtype] at ha
      exact Units.ne_zero I.val ha


    set α : Kˣ := Units.mk0 a ha_ne

    have hI_eq_span : (I.val : (FracIdeal K)ˣ).val =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (α : K) := by
      simp only [Subgroup.coe_subtype] at ha
      simp only [α, Units.mk0_val]
      exact ha
    have hI_eq_topi : I.val = toPrincipalIdeal (𝓞 K) K α := by
      apply Units.val_injective
      rw [coe_toPrincipalIdeal]
      exact hI_eq_span
    have hα_coprime : α ∈ UnitsCoprime_subgroup' K 𝔪 := by
      intro v hv
      have hI_cop := I.property v hv
      rw [hI_eq_topi] at hI_cop
      exact valuation_eq_one_of_spanSingleton_coprime' v α hI_cop.1 hI_cop.2

    set γ : UnitsCoprime_subgroup' K 𝔪 := ⟨α, hα_coprime⟩

    have hγ_eq : principalIdealMap 𝔪 γ = I := by
      apply Subtype.ext
      apply Units.val_injective
      simp only [principalIdealMap, MonoidHom.coe_mk, OneHom.coe_mk, coe_toPrincipalIdeal]
      exact hI_eq_span.symm

    refine ⟨Quot.mk _ γ, ?_⟩

    have key_map3 : (exactSeq_map3 𝔪)
        (Quot.mk (QuotientGroup.leftRel (UnitsCongruent_in_UnitsCoprime K 𝔪)) γ) =
        ((QuotientGroup.mk' (RayGroup K 𝔪)).comp (principalIdealMap 𝔪)) γ := by
      simp only [exactSeq_map3]
      erw [QuotientGroup.lift_mk']
    simp only [MonoidHom.comp_apply] at key_map3
    rw [key_map3, hγ_eq]
    rfl

theorem mk0_mem_FracIdealsCoprime_of_coprime (𝔪 : @Modulus K _ _)
    (I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)))
    (hI : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔭.asIdeal ∣ 𝔪.finitePartIdeal → ¬(𝔭.asIdeal ∣ (I : Ideal (NumberField.RingOfIntegers K)))) :
    FractionalIdeal.mk0 K I ∈ FracIdealsCoprime_subgroup K 𝔪 := by
  intro v hv
  constructor
  ·


    have hv_dvd : v.asIdeal ∣ 𝔪.finitePartIdeal := by
      simp only [Modulus.finitePartIdeal]
      apply dvd_trans (dvd_pow_self v.asIdeal (Nat.pos_of_ne_zero hv).ne')
      exact Finset.dvd_prod_of_mem _ (by
        simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
        exact hv)

    have hv_ndvd : ¬(v.asIdeal ∣ (I : Ideal (NumberField.RingOfIntegers K))) := hI v hv_dvd

    rw [Ideal.dvd_iff_le] at hv_ndvd
    obtain ⟨x, hxI, hxv⟩ := Set.not_subset.mp hv_ndvd

    refine ⟨algebraMap _ K x, ?_, ?_⟩
    · rw [FractionalIdeal.coe_mk0]
      exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨x, hxI, rfl⟩
    · rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hxv
  ·

    refine ⟨1, ?_, Valuation.map_one _⟩
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.coe_mk0]
    have hI_ne : (I : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥ := by
      intro h; exact nonZeroDivisors.ne_zero I.2 (by rwa [Ideal.zero_eq_bot])
    exact one_mem_inv_coe_ideal hI_ne

lemma classGroup_mk_comp_subtype_surjective (𝔪 : @Modulus K _ _) :
    Function.Surjective (ClassGroup.mk.comp
      (FracIdealsCoprime_subgroup K 𝔪).subtype) := by
  intro c
  obtain ⟨I, hI_class, hI_coprime⟩ :=
    lemma_21_7_ideal_class_coprime_rep (NumberField.RingOfIntegers K)
      𝔪.finitePartIdeal c 𝔪.finitePartIdeal_ne_bot
  have hI_mem := mk0_mem_FracIdealsCoprime_of_coprime 𝔪 I hI_coprime
  exact ⟨⟨FractionalIdeal.mk0 K I, hI_mem⟩, by
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact (ClassGroup.mk_mk0 K I).trans hI_class⟩

theorem exactSeq_surjective (𝔪 : @Modulus K _ _) :
    Function.Surjective (exactSeq_map4 𝔪) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (classGroup_mk_comp_subtype_surjective 𝔪) _

lemma Modulus.infSupportFinset_isReal (𝔪 : @Modulus K _ _)
    {w : NumberField.InfinitePlace K} (hw : w ∈ 𝔪.infSupportFinset) : w.IsReal := by
  simp only [Modulus.infSupportFinset, Set.Finite.mem_toFinset, Set.mem_preimage,
    Set.mem_setOf_eq] at hw
  by_contra h
  exact hw (𝔪.complex_zero w (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp h))

omit [NumberField K] in
lemma embedding_re_ne_zero {w : NumberField.InfinitePlace K} (hw : w.IsReal) (a : Kˣ) :
    (w.embedding (a : K)).re ≠ 0 := by
  intro h
  have hne : w.embedding (a : K) ≠ 0 := by
    rw [map_ne_zero_iff _ (RingHom.injective w.embedding)]; exact Units.ne_zero a
  exact hne (Complex.ext h (embedding_im_zero hw _))

noncomputable def signAtPlace {w : NumberField.InfinitePlace K}
    (_hw : w.IsReal) (α : Kˣ) : ZMod 2 :=
  if 0 < (w.embedding (α : K)).re then 0 else 1

omit [NumberField K] in
lemma signAtPlace_mul {w : NumberField.InfinitePlace K}
    (hw : w.IsReal) (a b : Kˣ) :
    signAtPlace hw (a * b) = signAtPlace hw a + signAtPlace hw b := by
  simp only [signAtPlace]
  have ha_im := embedding_im_zero hw (a : K)
  have hb_im := embedding_im_zero hw (b : K)
  have hab_re : (w.embedding ((a * b : Kˣ) : K)).re =
      (w.embedding (a : K)).re * (w.embedding (b : K)).re := by
    simp only [Units.val_mul, map_mul, Complex.mul_re, ha_im, hb_im, mul_zero, sub_zero]
  rw [hab_re]
  have ha_ne := embedding_re_ne_zero hw a
  have hb_ne := embedding_re_ne_zero hw b
  rcases lt_or_gt_of_ne ha_ne with ha_neg | ha_pos <;>
  rcases lt_or_gt_of_ne hb_ne with hb_neg | hb_pos
  · simp [not_lt.mpr ha_neg.le, not_lt.mpr hb_neg.le,
          mul_pos_of_neg_of_neg ha_neg hb_neg]; decide
  · simp [not_lt.mpr ha_neg.le, hb_pos,
          not_lt.mpr (mul_neg_of_neg_of_pos ha_neg hb_pos).le]
  · simp [ha_pos, not_lt.mpr hb_neg.le,
          not_lt.mpr (mul_neg_of_pos_of_neg ha_pos hb_neg).le]
  · simp [ha_pos, hb_pos, mul_pos ha_pos hb_pos]

omit [NumberField K] in
lemma signAtPlace_eq_zero_iff {w : NumberField.InfinitePlace K}
    (hw : w.IsReal) (α : Kˣ) :
    signAtPlace hw α = 0 ↔ 0 < (w.embedding (α : K)).re := by
  simp only [signAtPlace]
  constructor
  · intro h; split_ifs at h with hpos; exact hpos; exact absurd h one_ne_zero
  · intro h; simp [h]

noncomputable def signMapHom (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    UnitsCoprime_subgroup' K 𝔪 →*
      (𝔪.infSupportFinset → Multiplicative (ZMod 2)) where
  toFun α := fun ⟨w, hw⟩ =>
    Multiplicative.ofAdd (signAtPlace (𝔪.infSupportFinset_isReal hw) (α : Kˣ))
  map_one' := by
    funext ⟨w, hw⟩
    simp only [Pi.one_apply, signAtPlace]
    norm_num
  map_mul' a b := by
    funext ⟨w, hw⟩
    simp only [Pi.mul_apply]
    show Multiplicative.ofAdd (signAtPlace _ ((a * b : UnitsCoprime_subgroup' K 𝔪) : Kˣ)) =
      Multiplicative.ofAdd (signAtPlace _ (a : Kˣ)) *
      Multiplicative.ofAdd (signAtPlace _ (b : Kˣ))
    have hab : ((a * b : UnitsCoprime_subgroup' K 𝔪) : Kˣ) = (a : Kˣ) * (b : Kˣ) := by
      simp [Subgroup.coe_mul]
    rw [hab, signAtPlace_mul, ofAdd_add]

theorem coprime_rep_exists (𝔪 : @Modulus K _ _)
    (α : UnitsCoprime_subgroup' K 𝔪) :
    ∃ (a b : NumberField.RingOfIntegers K),
      IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal a) ∧
      IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal b) ∧
      algebraMap (NumberField.RingOfIntegers K) K a /
        algebraMap (NumberField.RingOfIntegers K) K b = ((α : Kˣ) : K) := by
  classical

  by_cases htriv : Subsingleton (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)
  · obtain ⟨a₀, b₀, hb₀, hab₀⟩ := IsFractionRing.div_surjective
      (NumberField.RingOfIntegers K) ((α : Kˣ) : K)
    haveI := htriv
    refine ⟨a₀, b₀, isUnit_of_subsingleton _, isUnit_of_subsingleton _, ?_⟩
    rw [← hab₀]
  ·
    rw [not_subsingleton_iff_nontrivial] at htriv; haveI := htriv

    obtain ⟨a₀, b₀, hb₀_mem, hab₀⟩ := IsFractionRing.div_surjective
      (NumberField.RingOfIntegers K) ((α : Kˣ) : K)

    have hα_ne : ((α : Kˣ) : K) ≠ 0 := Units.ne_zero (α : Kˣ)

    have hα_val : ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
        v.valuation K ((α : Kˣ) : K) = 1 := α.2

    set T := (𝔪.finite_support.preimage (f := Place.finite)
      (fun a _ b _ hab => by cases hab; rfl)).toFinset with hT_def
    have hT_mem : ∀ v : FinitePlace K, v ∈ T ↔ 𝔪 (Place.finite v) ≠ 0 := by
      intro v; simp [hT_def, Set.Finite.mem_toFinset]

    have hT_nonempty : T.Nonempty := by
      by_contra h_empty
      rw [Finset.not_nonempty_iff_eq_empty] at h_empty
      have hI_top : 𝔪.finitePartIdeal = ⊤ := by
        show T.prod (fun 𝔭 => 𝔭.asIdeal ^ 𝔪 (Place.finite 𝔭)) = ⊤
        simp [h_empty, Ideal.one_eq_top]
      exact absurd (Ideal.Quotient.nontrivial_iff.mp inferInstance) (not_not.mpr hI_top)

    let J : Ideal (NumberField.RingOfIntegers K) :=
    { carrier := {b | IsLocalization.IsInteger (NumberField.RingOfIntegers K)
        (algebraMap (NumberField.RingOfIntegers K) K b * ((α : Kˣ) : K))}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, IsLocalization.IsInteger, map_add, add_mul] at *
        obtain ⟨ca, hca⟩ := ha; obtain ⟨cb, hcb⟩ := hb
        exact ⟨ca + cb, by rw [map_add, hca, hcb]⟩
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero, zero_mul]; exact ⟨0, map_zero _⟩
      smul_mem' := fun c {b} hb => by
        simp only [Set.mem_setOf_eq, IsLocalization.IsInteger, smul_eq_mul, map_mul,
                   mul_assoc] at *
        obtain ⟨cb, hcb⟩ := hb; exact ⟨c * cb, by rw [map_mul, hcb]⟩ }

    have hb₀_in_J : b₀ ∈ J := by
      show IsLocalization.IsInteger _ _
      rw [← hab₀, mul_div_cancel₀]
      · exact ⟨a₀, rfl⟩
      · exact map_ne_zero_of_mem_nonZeroDivisors _
          (IsFractionRing.injective (NumberField.RingOfIntegers K) K) hb₀_mem

    have hJ_ne_bot : J ≠ ⊥ := by
      intro h
      have : b₀ ∈ (⊥ : Ideal (NumberField.RingOfIntegers K)) := h ▸ hb₀_in_J
      rw [Ideal.mem_bot] at this
      exact hα_ne (by rw [← hab₀]; simp [this])

    have hJ_not_le : ∀ v ∈ T, ¬(J ≤ v.asIdeal) := by
      intro v hv hle
      have hv_ne := (hT_mem v).mp hv
      have hv_ne_top : v.asIdeal ≠ ⊤ := v.isPrime.ne_top


      obtain ⟨c, hc_int, i, hi_mem, hc_notmem⟩ := Ideal.exist_integer_multiples_notMem (K := K)
        hv_ne_top ({0, 1} : Finset (Fin 2)) (fun i => if i = 0 then ((α : Kˣ) : K) else 1)
        (j := 1) (by simp) (by simp)

      have hc_is_int : IsLocalization.IsInteger (NumberField.RingOfIntegers K) c := by
        have := hc_int 1 (by simp); simpa using this

      have hcα_is_int : IsLocalization.IsInteger (NumberField.RingOfIntegers K)
          (c * ((α : Kˣ) : K)) := by
        have := hc_int 0 (by simp); simpa using this

      obtain ⟨b_int, hb_int⟩ := hc_is_int

      have hb_int_in_J : b_int ∈ J := by
        show IsLocalization.IsInteger _ _; rw [hb_int]; exact hcα_is_int

      have hb_int_mem : b_int ∈ v.asIdeal := hle hb_int_in_J

      have hv_c_ne1 : v.valuation K c ≠ 1 := by
        rw [← hb_int, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        rw [Ne, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
        exact not_not.mpr hb_int_mem

      have hv_α_eq1 : v.valuation K ((α : Kˣ) : K) = 1 := hα_val v hv_ne

      have hv_cα_ne1 : v.valuation K (c * ((α : Kˣ) : K)) ≠ 1 := by
        rw [map_mul, hv_α_eq1, mul_one]; exact hv_c_ne1

      obtain ⟨a_int, ha_int⟩ := hcα_is_int

      have ha_int_mem : a_int ∈ v.asIdeal := by
        rw [← not_not (a := a_int ∈ v.asIdeal)]
        rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
        intro h_eq
        exact hv_cα_ne1 (by
          rw [← ha_int, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, h_eq])


      rcases i with ⟨i, hi⟩
      interval_cases i
      ·
        simp only [Fin.mk_zero] at hc_notmem
        simp only [ite_true] at hc_notmem
        exact hc_notmem ((FractionalIdeal.mem_coeIdeal _).mpr ⟨a_int, ha_int_mem, ha_int⟩)
      ·
        simp only [Fin.mk_one, one_ne_zero, ite_false, mul_one] at hc_notmem
        exact hc_notmem ((FractionalIdeal.mem_coeIdeal _).mpr ⟨b_int, hb_int_mem, hb_int⟩)

    have ⟨b, hb_in_J, hb_avoid⟩ : ∃ b ∈ J, ∀ v ∈ T, b ∉ v.asIdeal := by
      by_contra h
      push_neg at h
      have hsub : (J : Set (NumberField.RingOfIntegers K)) ⊆
          ⋃ v ∈ (↑T : Set (FinitePlace K)), (v.asIdeal : Set _) := by
        intro x hx; obtain ⟨v, hv, hvx⟩ := h x hx
        exact Set.mem_biUnion (Finset.mem_coe.mpr hv) hvx
      obtain ⟨v₀, hv₀⟩ := hT_nonempty
      rw [Ideal.subset_union_prime_finite T.finite_toSet v₀ v₀
        (fun i _ _ _ => i.isPrime)] at hsub
      obtain ⟨i, hi, hle⟩ := hsub
      exact hJ_not_le i (Finset.mem_coe.mp hi) hle

    obtain ⟨a, ha_eq⟩ : IsLocalization.IsInteger (NumberField.RingOfIntegers K)
        (algebraMap (NumberField.RingOfIntegers K) K b * ((α : Kˣ) : K)) := hb_in_J

    have ha_avoid : ∀ v ∈ T, a ∉ v.asIdeal := by
      intro v hv ha_mem
      have hb_mem_or : b ∈ v.asIdeal := by
        by_contra hb_not_mem

        have hv_b : v.intValuation b = 1 :=
          IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hb_not_mem

        have hv_a : v.intValuation a ≠ 1 :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.not.mpr (not_not.mpr ha_mem))

        have : v.valuation K (algebraMap _ K a) = v.valuation K (algebraMap _ K b) *
            v.valuation K ((α : Kˣ) : K) := by
          rw [ha_eq, map_mul]
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
            IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
            hv_b, hα_val v ((hT_mem v).mp hv), mul_one] at this
        exact hv_a this
      exact hb_avoid v hv hb_mem_or

    have isUnit_of_avoid : ∀ (r : NumberField.RingOfIntegers K),
        (∀ v ∈ T, r ∉ v.asIdeal) →
        IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal r) := by
      intro r hr

      show IsUnit (Ideal.Quotient.mk
        (T.prod (fun 𝔭 => 𝔭.asIdeal ^ 𝔪 (Place.finite 𝔭))) r)

      have h1 : ∀ v ∈ T, Ideal.span {r} ⊔ (v.asIdeal ^ 𝔪 (Place.finite v)) = ⊤ := by
        intro v hv
        have hsup : Ideal.span {r} ⊔ v.asIdeal = ⊤ := by
          rw [Ideal.eq_top_iff_one]
          obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv v.isMaximal (hr v hv)
          exact Submodule.mem_sup.mpr
            ⟨y * r, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self r), i, hi, hyi⟩
        exact Ideal.sup_pow_eq_top hsup

      have h2 : Ideal.span {r} ⊔ T.prod (fun v => v.asIdeal ^ 𝔪 (Place.finite v)) = ⊤ :=
        Ideal.sup_prod_eq_top h1
      rw [Ideal.eq_top_iff_one] at h2
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h2
      rw [Ideal.mem_span_singleton] at hx; obtain ⟨c, rfl⟩ := hx
      have key : Ideal.Quotient.mk (T.prod (fun v => v.asIdeal ^ 𝔪 (Place.finite v))) r *
          Ideal.Quotient.mk (T.prod (fun v => v.asIdeal ^ 𝔪 (Place.finite v))) c = 1 := by
        have h3 : Ideal.Quotient.mk (T.prod (fun v => v.asIdeal ^ 𝔪 (Place.finite v)))
            (r * c + y) = 1 := by rw [hxy]; simp
        rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero, map_mul] at h3
      exact isUnit_of_mul_eq_one
        (b := Ideal.Quotient.mk (T.prod (fun v => v.asIdeal ^ 𝔪 (Place.finite v))) c) key

    refine ⟨a, b, isUnit_of_avoid a ha_avoid, isUnit_of_avoid b hb_avoid, ?_⟩

    have hb_ne : algebraMap (NumberField.RingOfIntegers K) K b ≠ 0 := by
      intro h
      have hb_zero : b = 0 := by
        rwa [map_eq_zero_iff _ (IsFractionRing.injective (NumberField.RingOfIntegers K) K)] at h
      obtain ⟨v₀, hv₀⟩ := hT_nonempty
      exact hb_avoid v₀ hv₀ (hb_zero ▸ v₀.asIdeal.zero_mem)
    rw [ha_eq, mul_div_cancel_left₀ _ hb_ne]

noncomputable def finitePartMapFn (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (α : UnitsCoprime_subgroup' K 𝔪) :
    (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)ˣ :=
  let h := coprime_rep_exists 𝔪 α
  let ha := h.choose_spec.choose_spec.1
  let hb := h.choose_spec.choose_spec.2.1
  ha.unit * hb.unit⁻¹

theorem coprime_rep_well_def (𝔪 : @Modulus K _ _)
    {a b c d : NumberField.RingOfIntegers K}
    (ha : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal a))
    (hb : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal b))
    (hc : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal c))
    (hd : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal d))
    (hab : algebraMap (NumberField.RingOfIntegers K) K a /
             algebraMap (NumberField.RingOfIntegers K) K b =
           algebraMap (NumberField.RingOfIntegers K) K c /
             algebraMap (NumberField.RingOfIntegers K) K d) :
    ha.unit * hb.unit⁻¹ = hc.unit * hd.unit⁻¹ := by

  by_cases htriv : Subsingleton (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)
  · haveI := htriv
    exact Subsingleton.elim _ _
  · rw [not_subsingleton_iff_nontrivial] at htriv
    haveI := htriv

    have hb_ne : algebraMap (NumberField.RingOfIntegers K) K b ≠ 0 := by
      intro heq
      exact hb.ne_zero (show Ideal.Quotient.mk 𝔪.finitePartIdeal b = 0 from by
        have : b = 0 := IsFractionRing.injective _ K (by rwa [map_zero])
        rw [this, map_zero])
    have hd_ne : algebraMap (NumberField.RingOfIntegers K) K d ≠ 0 := by
      intro heq
      exact hd.ne_zero (show Ideal.Quotient.mk 𝔪.finitePartIdeal d = 0 from by
        have : d = 0 := IsFractionRing.injective _ K (by rwa [map_zero])
        rw [this, map_zero])

    have h_integral : a * d = b * c := IsFractionRing.injective _ K (by
      simp only [map_mul]
      have h := (div_eq_div_iff hb_ne hd_ne).mp hab
      rw [mul_comm (algebraMap (NumberField.RingOfIntegers K) K c)
          (algebraMap (NumberField.RingOfIntegers K) K b)] at h
      exact h)

    have h_quot : Ideal.Quotient.mk 𝔪.finitePartIdeal a *
                  Ideal.Quotient.mk 𝔪.finitePartIdeal d =
                  Ideal.Quotient.mk 𝔪.finitePartIdeal b *
                  Ideal.Quotient.mk 𝔪.finitePartIdeal c := by
      rw [← map_mul, ← map_mul, h_integral]

    have key : ha.unit * hd.unit = hb.unit * hc.unit := by
      ext; simp [IsUnit.unit_spec, h_quot]

    exact mul_right_cancel (b := hb.unit * hd.unit) (by
      calc ha.unit * hb.unit⁻¹ * (hb.unit * hd.unit)
          = ha.unit * (hb.unit⁻¹ * hb.unit) * hd.unit := by simp only [mul_assoc]
        _ = ha.unit * hd.unit := by simp
        _ = hb.unit * hc.unit := key
        _ = hc.unit * hb.unit := mul_comm _ _
        _ = hc.unit * (hd.unit⁻¹ * hd.unit) * hb.unit := by simp
        _ = hc.unit * hd.unit⁻¹ * (hd.unit * hb.unit) := by simp only [mul_assoc]
        _ = hc.unit * hd.unit⁻¹ * (hb.unit * hd.unit) := by rw [mul_comm hd.unit hb.unit])

noncomputable def finitePartMapHom (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    UnitsCoprime_subgroup' K 𝔪 →*
      (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)ˣ where
  toFun := finitePartMapFn K 𝔪
  map_one' := by
    show finitePartMapFn K 𝔪 1 = 1
    simp only [finitePartMapFn]
    have h := coprime_rep_exists 𝔪 (1 : UnitsCoprime_subgroup' K 𝔪)
    have ha := h.choose_spec.choose_spec.1
    have hb := h.choose_spec.choose_spec.2.1
    have heq' := h.choose_spec.choose_spec.2.2
    have h1u : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal (1 : 𝓞 K)) := isUnit_one

    simp only [Subgroup.coe_one, Units.val_one] at heq'


    have := coprime_rep_well_def 𝔪 ha hb h1u h1u (by rw [map_one, div_one]; exact heq')
    rw [this]
    simp
  map_mul' := fun x y => by
    show finitePartMapFn K 𝔪 (x * y) = finitePartMapFn K 𝔪 x * finitePartMapFn K 𝔪 y
    simp only [finitePartMapFn]

    have hx := coprime_rep_exists 𝔪 x
    have hy := coprime_rep_exists 𝔪 y
    have hxy := coprime_rep_exists 𝔪 (x * y)
    have hax := hx.choose_spec.choose_spec.1
    have hbx := hx.choose_spec.choose_spec.2.1
    have heqx := hx.choose_spec.choose_spec.2.2
    have hay := hy.choose_spec.choose_spec.1
    have hby := hy.choose_spec.choose_spec.2.1
    have heqy := hy.choose_spec.choose_spec.2.2
    have haxy := hxy.choose_spec.choose_spec.1
    have hbxy := hxy.choose_spec.choose_spec.2.1
    have heqxy := hxy.choose_spec.choose_spec.2.2

    have haxay : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal
        (hx.choose * hy.choose)) := by
      rw [map_mul]; exact hax.mul hay
    have hbxby : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal
        (hx.choose_spec.choose * hy.choose_spec.choose)) := by
      rw [map_mul]; exact hbx.mul hby
    simp only [Subgroup.coe_mul, Units.val_mul] at heqxy
    have hprod : algebraMap (𝓞 K) K (hx.choose * hy.choose) /
        algebraMap (𝓞 K) K (hx.choose_spec.choose * hy.choose_spec.choose) =
        ((x : Kˣ) : K) * ((y : Kˣ) : K) := by
      trans (algebraMap (𝓞 K) K hx.choose / algebraMap (𝓞 K) K hx.choose_spec.choose *
             (algebraMap (𝓞 K) K hy.choose / algebraMap (𝓞 K) K hy.choose_spec.choose))
      · simp only [map_mul, div_mul_div_comm]
      · rw [heqx, heqy]
    have hwd := coprime_rep_well_def 𝔪 haxy hbxy haxay hbxby
      (by rw [hprod]; exact heqxy)
    have key1 : haxay.unit = hax.unit * hay.unit := by
      ext; simp only [Units.val_mul, IsUnit.unit_spec, map_mul]
    have key2 : hbxby.unit = hbx.unit * hby.unit := by
      ext; simp only [Units.val_mul, IsUnit.unit_spec, map_mul]
    rw [hwd, key1, key2, mul_inv_rev]
    calc hax.unit * hay.unit * (hby.unit⁻¹ * hbx.unit⁻¹)
        = hax.unit * (hay.unit * hby.unit⁻¹) * hbx.unit⁻¹ := by
          simp only [mul_assoc]
      _ = hax.unit * hbx.unit⁻¹ * (hay.unit * hby.unit⁻¹) :=
          mul_right_comm _ _ _

lemma finset_prod_ideal_le_factor {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → Ideal R) (j : ι) (hj : j ∈ S) :
    S.prod f ≤ f j := by
  induction S using Finset.cons_induction with
  | empty => simp at hj
  | cons i s hi ih =>
    rw [Finset.prod_cons]
    rcases Finset.mem_cons.mp hj with rfl | hjs
    · exact Ideal.mul_le_right
    · exact le_trans Ideal.mul_le_left (ih hjs)

lemma unit_mod_ideal_not_in_prime {R : Type*} [CommRing R]
    {I 𝔭 : Ideal R} (hI𝔭 : I ≤ 𝔭) (h𝔭 : 𝔭 ≠ ⊤) {b : R}
    (hb : IsUnit (Ideal.Quotient.mk I b)) : b ∉ 𝔭 := by
  intro hb_mem
  let f := Ideal.Quotient.lift I (Ideal.Quotient.mk 𝔭) (fun r hr =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hI𝔭 hr))
  have hunit : IsUnit (f (Ideal.Quotient.mk I b)) := hb.map f
  simp only [f, Ideal.Quotient.lift_mk] at hunit
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb_mem] at hunit
  haveI : Nontrivial (R ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.mpr h𝔭
  exact not_isUnit_zero hunit

theorem coprime_rep_unit_eq_one_iff (𝔪 : @Modulus K _ _)
    {a b : NumberField.RingOfIntegers K}
    (ha : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal a))
    (hb : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal b))
    (hab : algebraMap (NumberField.RingOfIntegers K) K a /
             algebraMap (NumberField.RingOfIntegers K) K b = ((α : Kˣ) : K)) :
    ha.unit * hb.unit⁻¹ = 1 ↔
      ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
        v.valuation K (((α : Kˣ) : K) - 1) ≤
          ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ))) := by
  classical


  have step1 : ha.unit * hb.unit⁻¹ = 1 ↔ a - b ∈ 𝔪.finitePartIdeal := by
    rw [mul_inv_eq_one]
    constructor
    · intro h
      have h' : (ha.unit : 𝓞 K ⧸ 𝔪.finitePartIdeal) = (hb.unit : 𝓞 K ⧸ 𝔪.finitePartIdeal) :=
        congr_arg Units.val h
      simp only [IsUnit.unit_spec] at h'
      exact Ideal.Quotient.eq.mp h'
    · intro h
      ext; simp only [IsUnit.unit_spec]; exact Ideal.Quotient.eq.mpr h
  rw [step1]

  set S := (𝔪.finite_support.preimage (f := Place.finite)
    (fun a _ b _ hab => by cases hab; rfl)).toFinset with hS_def


  have hb_ne_zero : (algebraMap (NumberField.RingOfIntegers K) K) b ≠ 0 := by
    intro h0
    simp [h0] at hab
    exact (Units.ne_zero α) hab.symm


  have hα_sub : ((α : Kˣ) : K) - 1 =
      algebraMap (NumberField.RingOfIntegers K) K (a - b) /
        algebraMap (NumberField.RingOfIntegers K) K b := by
    rw [← hab, map_sub]; field_simp

  have hv_in_S : ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → v ∈ S := by
    intro v hv
    simp only [hS_def, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
    exact hv

  have hI_le : ∀ v ∈ S, 𝔪.finitePartIdeal ≤ v.asIdeal ^ 𝔪 (Place.finite v) := by
    intro v hv
    exact finset_prod_ideal_le_factor S _ v hv

  have hb_not_mem : ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → b ∉ v.asIdeal := by
    intro v hv
    exact unit_mod_ideal_not_in_prime
      (le_trans (hI_le v (hv_in_S v hv)) (Ideal.pow_le_self hv))
      v.isPrime.ne_top hb


  have hvb_one : ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
      v.intValuation b = 1 := by
    intro v hv
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr (hb_not_mem v hv)

  have hval_eq : ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
      v.valuation K (((α : Kˣ) : K) - 1) = v.intValuation (a - b) := by
    intro v hv
    rw [hα_sub, Valuation.map_div,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        hvb_one v hv, div_one]

  have hval_mem : ∀ v : FinitePlace K, ∀ n : ℕ,
      v.intValuation (a - b) ≤ ↑(Multiplicative.ofAdd (-(n : ℤ))) ↔
        a - b ∈ v.asIdeal ^ n := by
    intro v n
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v (a - b) n

  constructor
  ·
    intro hmem v hv
    rw [hval_eq v hv, hval_mem v]
    exact hI_le v (hv_in_S v hv) hmem
  ·
    intro hval

    have hcrt : S.inf (fun 𝔭 => 𝔭.asIdeal ^ 𝔪 (Place.finite 𝔭)) =
        S.prod (fun 𝔭 => 𝔭.asIdeal ^ 𝔪 (Place.finite 𝔭)) :=
      IsDedekindDomain.HeightOneSpectrum.inf_pow_eq_prod S
        (fun 𝔭 => 𝔪 (Place.finite 𝔭)) id (fun _ hi _ hj hij => hij)

    rw [show 𝔪.finitePartIdeal = S.prod (fun 𝔭 => 𝔭.asIdeal ^ 𝔪 (Place.finite 𝔭)) from rfl,
        ← hcrt, Submodule.mem_finsetInf]
    intro v hv
    have hv_ne : 𝔪 (Place.finite v) ≠ 0 := by
      simp only [hS_def, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq] at hv
      exact hv
    rw [← hval_mem v, ← hval_eq v hv_ne]
    exact hval v hv_ne

theorem finitePartMapHom_ker_iff (𝔪 : @Modulus K _ _)
    (α : UnitsCoprime_subgroup' K 𝔪) :
    finitePartMapHom K 𝔪 α = 1 ↔
      ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
        v.valuation K (((α : Kˣ) : K) - 1) ≤
          ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ))) := by

  show finitePartMapFn K 𝔪 α = 1 ↔ _
  simp only [finitePartMapFn]

  have h := coprime_rep_exists 𝔪 α
  have ha := h.choose_spec.choose_spec.1
  have hb := h.choose_spec.choose_spec.2.1
  have heq := h.choose_spec.choose_spec.2.2

  exact coprime_rep_unit_eq_one_iff (α := (α : Kˣ)) 𝔪 ha hb heq

theorem weak_approx_nonzero_with_val_and_sign {K : Type*} [Field K] [NumberField K]
    (𝔪 : @Modulus K _ _)
    (pos : 𝔪.infSupportFinset → Prop) [DecidablePred pos] :
    ∃ (x : K) (_ : x ≠ 0),
      (∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → v.valuation K x = 1) ∧
      (∀ (w : NumberField.InfinitePlace K) (hw : w ∈ 𝔪.infSupportFinset),
        (pos ⟨w, hw⟩ → 0 < (w.embedding x).re) ∧
        (¬ pos ⟨w, hw⟩ → (w.embedding x).re < 0)) := by
  classical

  let S_fin : Finset (FinitePlace K) :=
    (𝔪.finite_support.preimage (f := Place.finite)
      (fun a _ b _ hab => by cases hab; rfl)).toFinset
  let S_inf := 𝔪.infSupportFinset

  let w₀ : NumberField.InfinitePlace K := Classical.arbitrary _
  let S_inf' : Finset (NumberField.InfinitePlace K) := S_inf ∪ {w₀}

  let ι := (↥S_fin) ⊕ (↥S_inf')

  let absVals : ι → AbsoluteValue K ℝ := fun i => match i with
    | .inl ⟨v, _⟩ => FinitePlace.toAbsoluteValue v
    | .inr ⟨w, _⟩ => w.val

  have hNontrivial : ∀ i, (absVals i).IsNontrivial := fun i => match i with
    | .inl ⟨v, _⟩ => FinitePlace.toAbsoluteValue_isNontrivial v
    | .inr ⟨w, _⟩ => by
        show w.val.IsNontrivial
        refine ⟨2, two_ne_zero, ?_⟩
        rw [show w.val 2 = w 2 from rfl,
            ← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat]
        simp

  have hIneq : ∀ i j, i ≠ j → ¬ (absVals i).IsEquiv (absVals j) := by
    intro i j hij
    match i, j with
    | .inl ⟨v₁, _⟩, .inl ⟨v₂, _⟩ =>
      have hne : v₁ ≠ v₂ := fun h => hij (by subst h; rfl)
      exact FinitePlace.toAbsoluteValue_pairwise_inequiv v₁ v₂ hne
    | .inr ⟨w₁, _⟩, .inr ⟨w₂, _⟩ =>
      have hne : w₁ ≠ w₂ := fun h => hij (by subst h; rfl)
      intro heq
      exact hne (NumberField.InfinitePlace.eq_iff_isEquiv.mpr (show w₁.val.IsEquiv w₂.val from heq))
    | .inl ⟨v, _⟩, .inr ⟨w, _⟩ =>
      intro heq

      have hna_v : IsNonarchimedean (FinitePlace.toAbsoluteValue v) := by
        intro a b
        exact NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v a b

      have hna_w : IsNonarchimedean (w.val) := by
        intro a b
        have h1 := hna_v a b
        change FinitePlace.toAbsoluteValue v (a + b) ≤
          FinitePlace.toAbsoluteValue v a ⊔ FinitePlace.toAbsoluteValue v b at h1
        rcases le_total (FinitePlace.toAbsoluteValue v a) (FinitePlace.toAbsoluteValue v b) with hab | hab
        · exact le_trans ((heq (a + b) b).mp (le_trans h1 (sup_le hab le_rfl))) le_sup_right
        · exact le_trans ((heq (a + b) a).mp (le_trans h1 (sup_le le_rfl hab))) le_sup_left

      have h2 : w.val 2 = 2 := by
        rw [show w.val 2 = w 2 from rfl,
            ← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat, Complex.norm_ofNat]
      have hle := hna_w 1 1
      simp only [show (1 : K) + 1 = 2 from by ring] at hle
      rw [h2, map_one] at hle; simp only [max_self] at hle; linarith
    | .inr ⟨w, _⟩, .inl ⟨v, _⟩ =>
      intro heq
      have hna_v : IsNonarchimedean (FinitePlace.toAbsoluteValue v) := by
        intro a b
        exact NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v a b
      have heq' := AbsoluteValue.IsEquiv.symm heq
      have hna_w : IsNonarchimedean (w.val) := by
        intro a b
        have h1 := hna_v a b
        change FinitePlace.toAbsoluteValue v (a + b) ≤
          FinitePlace.toAbsoluteValue v a ⊔ FinitePlace.toAbsoluteValue v b at h1
        rcases le_total (FinitePlace.toAbsoluteValue v a) (FinitePlace.toAbsoluteValue v b) with hab | hab
        · exact le_trans ((heq' (a + b) b).mp (le_trans h1 (sup_le hab le_rfl))) le_sup_right
        · exact le_trans ((heq' (a + b) a).mp (le_trans h1 (sup_le le_rfl hab))) le_sup_left
      have h2 : w.val 2 = 2 := by
        rw [show w.val 2 = w 2 from rfl,
            ← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat, Complex.norm_ofNat]
      have hle := hna_w 1 1
      simp only [show (1 : K) + 1 = 2 from by ring] at hle
      rw [h2, map_one] at hle; simp only [max_self] at hle; linarith

  let target : ι → K := fun i => match i with
    | .inl _ => 1
    | .inr ⟨w, hw⟩ =>
      if h : w ∈ S_inf then
        if pos ⟨w, h⟩ then 1 else -1
      else 1
  let ε : ι → ℝ := fun _ => 1 / 2

  obtain ⟨x, hx⟩ := weak_approximation_theorem absVals hNontrivial hIneq target ε
    (fun _ => by norm_num)

  refine ⟨x, ?_, ?_, ?_⟩
  ·
    intro hx0
    have hmem : w₀ ∈ S_inf' := Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hi := hx (.inr ⟨w₀, hmem⟩)
    simp only [target, absVals] at hi
    rw [hx0] at hi

    split_ifs at hi with h1 h2
    all_goals (
      simp only [ε, show (0 : K) - 1 = -1 from by ring,
        show (0 : K) - -1 = 1 from by ring,
        AbsoluteValue.map_neg, map_one] at hi; linarith)

  ·
    intro v hv
    have hvmem : v ∈ S_fin := by
      simp only [S_fin, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
      exact hv
    have hi := hx (.inl ⟨v, hvmem⟩)
    simp only [target, absVals, FinitePlace.toAbsoluteValue] at hi

    have hi' : NumberField.HeightOneSpectrum.adicAbv K v (x - 1) < 1 / 2 := by
      simp only [ε] at hi; exact hi
    have hlt1 : NumberField.HeightOneSpectrum.adicAbv K v (x - 1) < 1 := by linarith
    have hna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
    have h1_val : NumberField.HeightOneSpectrum.adicAbv K v 1 = 1 := map_one _
    have hlt_strict : NumberField.HeightOneSpectrum.adicAbv K v (x - 1) <
        NumberField.HeightOneSpectrum.adicAbv K v 1 := by rw [h1_val]; exact hlt1
    have hmax := IsNonarchimedean.add_eq_max_of_ne hna hlt_strict.ne
    rw [sub_add_cancel] at hmax
    have hxeq1 : NumberField.HeightOneSpectrum.adicAbv K v x = 1 := by
      rw [hmax, h1_val, max_eq_right (le_of_lt hlt1)]

    have hne0 := NumberField.HeightOneSpectrum.absNorm_ne_zero (R := 𝓞 K) v
    have hne1 := ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (R := 𝓞 K) v)
    rw [NumberField.HeightOneSpectrum.adicAbv_def] at hxeq1
    have hnnr : WithZeroMulInt.toNNReal hne0 (v.valuation K x) = 1 := by exact_mod_cast hxeq1
    exact (WithZeroMulInt.toNNReal_eq_one_iff _ hne0 hne1).mp hnnr
  ·
    intro w hw
    have hwmem : w ∈ S_inf' := Finset.mem_union_left _ hw
    have hi := hx (.inr ⟨w, hwmem⟩)
    simp only [target, absVals, show w ∈ S_inf from hw, dite_true] at hi

    have hw_real := 𝔪.infSupportFinset_isReal hw

    have him_eq : ∀ y : K, (w.embedding y).im = 0 := by
      intro y
      have hr := NumberField.InfinitePlace.isReal_iff.mp hw_real
      have hconj : starRingEnd ℂ (w.embedding y) = w.embedding y :=
        RingHom.congr_fun hr y
      rwa [Complex.conj_eq_iff_im] at hconj

    have hw_val_eq : ∀ y : K, w.val y = ‖w.embedding y‖ := by
      intro y; exact (NumberField.InfinitePlace.norm_embedding_eq w y).symm

    have norm_eq_abs_re : ∀ y : K, ‖w.embedding y‖ = |((w.embedding y).re)| := by
      intro y
      have hze : (w.embedding y) = ↑(w.embedding y).re :=
        Complex.ext rfl (by simp [him_eq y])
      rw [hze, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
    constructor
    ·
      intro hpos
      simp only [hpos, ite_true] at hi

      have habs : |((w.embedding (x - 1)).re)| < 1 / 2 := by
        have : w.val (x - 1) = ‖w.embedding (x - 1)‖ := hw_val_eq (x - 1)
        rw [this, norm_eq_abs_re (x - 1)] at hi
        exact hi
      rw [map_sub, Complex.sub_re, map_one, Complex.one_re, abs_lt] at habs
      linarith [habs.1]
    ·
      intro hnpos
      simp only [hnpos, ite_false] at hi
      have habs : |((w.embedding (x - (-1))).re)| < 1 / 2 := by
        have : w.val (x - (-1)) = ‖w.embedding (x - (-1))‖ := hw_val_eq (x - (-1))
        rw [this, norm_eq_abs_re (x - (-1))] at hi
        exact hi
      rw [map_sub, map_neg, map_one, Complex.sub_re, Complex.neg_re, Complex.one_re] at habs
      rw [show (w.embedding x).re - -1 = (w.embedding x).re + 1 from by ring, abs_lt] at habs
      linarith [habs.2]

theorem weak_approx_sign_coprime {K : Type*} [Field K] [NumberField K]
    (𝔪 : @Modulus K _ _)
    (s : 𝔪.infSupportFinset → Multiplicative (ZMod 2)) :
    ∃ (α : Kˣ),
      (∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → v.valuation K (α : K) = 1) ∧
      (∀ (w : NumberField.InfinitePlace K) (hw : w ∈ 𝔪.infSupportFinset),
        Multiplicative.ofAdd (signAtPlace (𝔪.infSupportFinset_isReal hw) α) = s ⟨w, hw⟩) := by
  classical

  let pos : 𝔪.infSupportFinset → Prop := fun wh => s wh = 1
  obtain ⟨x, hx_ne, hval, hsign⟩ := weak_approx_nonzero_with_val_and_sign 𝔪 pos

  refine ⟨Units.mk0 x hx_ne, hval, ?_⟩
  intro w hw
  simp only [signAtPlace, Units.val_mk0]
  have ⟨hpos_case, hneg_case⟩ := hsign w hw


  by_cases hp : pos ⟨w, hw⟩
  ·
    have hre_pos := hpos_case hp
    simp [hre_pos]
    change Multiplicative.ofAdd (0 : ZMod 2) = s ⟨w, hw⟩
    exact hp.symm
  ·
    have hre_neg := hneg_case hp
    simp only [show ¬(0 < (w.embedding x).re) from not_lt.mpr (le_of_lt hre_neg), ite_false]
    change Multiplicative.ofAdd (1 : ZMod 2) = s ⟨w, hw⟩


    have : ∀ (a : Multiplicative (ZMod 2)),
        a = Multiplicative.ofAdd 0 ∨ a = Multiplicative.ofAdd 1 := by
      intro a
      rcases Multiplicative.ofAdd.surjective a with ⟨b, rfl⟩
      fin_cases b <;> first | left; rfl | right; rfl
    rcases this (s ⟨w, hw⟩) with h | h
    · exfalso; exact hp h
    · exact h.symm

theorem signMapHom_surjective (𝔪 : @Modulus K _ _) :
    Function.Surjective (signMapHom K 𝔪) := by
  intro s
  exact signMapHom_surjective_aux 𝔪 s
where
  signMapHom_surjective_aux : ∀ (𝔪 : @Modulus K _ _)
      (s : 𝔪.infSupportFinset → Multiplicative (ZMod 2)),
      ∃ α : UnitsCoprime_subgroup' K 𝔪, signMapHom K 𝔪 α = s := by
    intro 𝔪 s


    obtain ⟨α, hcoprime, hsigns⟩ := weak_approx_sign_coprime 𝔪 s

    have hmem : (α : Kˣ) ∈ UnitsCoprime_subgroup' K 𝔪 := by
      intro v hv
      exact hcoprime v hv
    refine ⟨⟨α, hmem⟩, ?_⟩

    funext ⟨w, hw⟩
    simp only [signMapHom]
    exact hsigns w hw

theorem weak_approx_coprime_sign_finitePart {K : Type*} [Field K] [NumberField K]
    (𝔪 : @Modulus K _ _)
    (u : (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)ˣ) :
    ∃ (α : UnitsCoprime_subgroup' K 𝔪),
      signMapHom K 𝔪 α = 1 ∧ finitePartMapHom K 𝔪 α = u := by
  classical

  by_cases htriv : Subsingleton (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)
  · haveI := htriv
    exact ⟨1, by simp [MonoidHom.map_one], by simp [MonoidHom.map_one, Subsingleton.eq_one u]⟩
  · rw [not_subsingleton_iff_nontrivial] at htriv; haveI := htriv

    obtain ⟨r, hr_lift⟩ : ∃ r : 𝓞 K,
        Ideal.Quotient.mk 𝔪.finitePartIdeal r = (u : 𝓞 K ⧸ 𝔪.finitePartIdeal) :=
      Ideal.Quotient.mk_surjective (u : 𝓞 K ⧸ 𝔪.finitePartIdeal)
    have hr_unit : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal r) := by
      rw [hr_lift]; exact u.isUnit
    have hr_ne_zero : r ≠ 0 := by
      intro h; rw [h, map_zero] at hr_lift; exact not_isUnit_zero (hr_lift ▸ u.isUnit)
    have halg_ne : algebraMap (𝓞 K) K r ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ K)]

    let α_r : Kˣ := Units.mk0 (algebraMap (𝓞 K) K r) halg_ne
    have hα_r_coprime : (α_r : Kˣ) ∈ UnitsCoprime_subgroup' K 𝔪 := by
      intro v hv
      have hr_not_in_v : r ∉ v.asIdeal := by
        apply unit_mod_ideal_not_in_prime _ v.isPrime.ne_top hr_unit
        set S := (𝔪.finite_support.preimage (f := Place.finite)
          (fun a _ b _ hab => by cases hab; rfl)).toFinset with hS_def
        have hvmem : v ∈ S := by
          simp only [hS_def, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
          exact hv
        exact le_trans (finset_prod_ideal_le_factor S _ v hvmem) (Ideal.pow_le_self hv)

      simp only [Units.val_mk0, α_r]
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hr_not_in_v
    let α₀ : UnitsCoprime_subgroup' K 𝔪 := ⟨α_r, hα_r_coprime⟩


    have hfp_α₀ : finitePartMapHom K 𝔪 α₀ = u := by
      show finitePartMapFn K 𝔪 α₀ = u
      simp only [finitePartMapFn]
      have h := coprime_rep_exists 𝔪 α₀
      have ha_rep := h.choose_spec.choose_spec.1
      have hb_rep := h.choose_spec.choose_spec.2.1
      have heq_rep := h.choose_spec.choose_spec.2.2
      have h1_unit : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal (1 : 𝓞 K)) := isUnit_one
      have heq_our : algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K 1 = ((α₀ : Kˣ) : K) := by
        simp [Units.val_mk0, α_r, α₀]

      have hwd := coprime_rep_well_def 𝔪 ha_rep hb_rep hr_unit h1_unit
        (by rw [heq_our]; exact heq_rep)
      rw [hwd]
      have hu_eq : hr_unit.unit = u := by ext; simp [IsUnit.unit_spec, hr_lift]
      have h1_eq : h1_unit.unit = 1 := by ext; simp
      simp [hu_eq, h1_eq]


    let S_fin : Finset (FinitePlace K) :=
      (𝔪.finite_support.preimage (f := Place.finite)
        (fun a _ b _ hab => by cases hab; rfl)).toFinset
    let S_inf := 𝔪.infSupportFinset
    let w₀ : NumberField.InfinitePlace K := Classical.arbitrary _
    let S_inf' : Finset (NumberField.InfinitePlace K) := S_inf ∪ {w₀}
    let ι := (↥S_fin) ⊕ (↥S_inf')
    let absVals : ι → AbsoluteValue K ℝ := fun i => match i with
      | .inl ⟨v, _⟩ => FinitePlace.toAbsoluteValue v
      | .inr ⟨w, _⟩ => w.val
    have hNontrivial : ∀ i, (absVals i).IsNontrivial := fun i => match i with
      | .inl ⟨v, _⟩ => FinitePlace.toAbsoluteValue_isNontrivial v
      | .inr ⟨w, _⟩ => by
          show w.val.IsNontrivial
          refine ⟨2, two_ne_zero, ?_⟩
          rw [show w.val 2 = w 2 from rfl,
              ← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat]
          simp
    have hIneq : ∀ i j, i ≠ j → ¬ (absVals i).IsEquiv (absVals j) := by
      intro i j hij
      match i, j with
      | .inl ⟨v₁, _⟩, .inl ⟨v₂, _⟩ =>
        have hne : v₁ ≠ v₂ := fun h => hij (by subst h; rfl)
        exact FinitePlace.toAbsoluteValue_pairwise_inequiv v₁ v₂ hne
      | .inr ⟨w₁, _⟩, .inr ⟨w₂, _⟩ =>
        have hne : w₁ ≠ w₂ := fun h => hij (by subst h; rfl)
        intro heq
        exact hne (NumberField.InfinitePlace.eq_iff_isEquiv.mpr
          (show w₁.val.IsEquiv w₂.val from heq))
      | .inl ⟨v, _⟩, .inr ⟨w, _⟩ =>
        intro heq
        have hna_v : IsNonarchimedean (FinitePlace.toAbsoluteValue v) := by
          intro a b; exact NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v a b
        have hna_w : IsNonarchimedean (w.val) := by
          intro a b
          have h1 := hna_v a b
          change FinitePlace.toAbsoluteValue v (a + b) ≤
            FinitePlace.toAbsoluteValue v a ⊔ FinitePlace.toAbsoluteValue v b at h1
          rcases le_total (FinitePlace.toAbsoluteValue v a)
            (FinitePlace.toAbsoluteValue v b) with hab | hab
          · exact le_trans ((heq (a + b) b).mp (le_trans h1 (sup_le hab le_rfl))) le_sup_right
          · exact le_trans ((heq (a + b) a).mp (le_trans h1 (sup_le le_rfl hab))) le_sup_left
        have h2 : w.val 2 = 2 := by
          rw [show w.val 2 = w 2 from rfl,
              ← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat, Complex.norm_ofNat]
        have hle := hna_w 1 1
        simp only [show (1 : K) + 1 = 2 from by ring] at hle
        rw [h2, map_one] at hle; simp only [max_self] at hle; linarith
      | .inr ⟨w, _⟩, .inl ⟨v, _⟩ =>
        intro heq
        have hna_v : IsNonarchimedean (FinitePlace.toAbsoluteValue v) := by
          intro a b; exact NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v a b
        have heq' := AbsoluteValue.IsEquiv.symm heq
        have hna_w : IsNonarchimedean (w.val) := by
          intro a b
          have h1 := hna_v a b
          change FinitePlace.toAbsoluteValue v (a + b) ≤
            FinitePlace.toAbsoluteValue v a ⊔ FinitePlace.toAbsoluteValue v b at h1
          rcases le_total (FinitePlace.toAbsoluteValue v a)
            (FinitePlace.toAbsoluteValue v b) with hab | hab
          · exact le_trans ((heq' (a + b) b).mp (le_trans h1 (sup_le hab le_rfl))) le_sup_right
          · exact le_trans ((heq' (a + b) a).mp (le_trans h1 (sup_le le_rfl hab))) le_sup_left
        have h2 : w.val 2 = 2 := by
          rw [show w.val 2 = w 2 from rfl,
              ← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat, Complex.norm_ofNat]
        have hle := hna_w 1 1
        simp only [show (1 : K) + 1 = 2 from by ring] at hle
        rw [h2, map_one] at hle; simp only [max_self] at hle; linarith

    let target : ι → K := fun i => match i with
      | .inl _ => algebraMap (𝓞 K) K r
      | .inr _ => 1


    let εfin (v : FinitePlace K) : ℝ :=
      min (1 / 2) ((Ideal.absNorm v.asIdeal : ℝ) ^
        (-(𝔪 (Place.finite v) - 1 : ℤ)))
    let ε : ι → ℝ := fun i => match i with
      | .inl ⟨v, _⟩ => εfin v
      | .inr _ => 1 / 2
    have hε_pos : ∀ i, 0 < ε i := by
      intro i; match i with
      | .inl ⟨v, _⟩ =>
        show 0 < min (1 / 2) _
        apply lt_min (by norm_num)
        apply zpow_pos
        have h := NumberField.HeightOneSpectrum.absNorm_ne_zero (R := 𝓞 K) v
        exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by exact_mod_cast h))
      | .inr _ => norm_num

    obtain ⟨x, hx⟩ := weak_approximation_theorem absVals hNontrivial hIneq target ε hε_pos

    have hx_ne : x ≠ 0 := by
      intro hx0
      have hmem : w₀ ∈ S_inf' := Finset.mem_union_right _ (Finset.mem_singleton_self _)
      have hi := hx (.inr ⟨w₀, hmem⟩)
      simp only [target, absVals, ε] at hi
      rw [hx0, show (0 : K) - 1 = -1 from by ring, AbsoluteValue.map_neg, map_one] at hi
      linarith

    have hx_coprime : ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
        v.valuation K x = 1 := by
      intro v hv
      have hvmem : v ∈ S_fin := by
        simp only [S_fin, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]; exact hv
      have hi := hx (.inl ⟨v, hvmem⟩)
      simp only [target, absVals, FinitePlace.toAbsoluteValue, ε, εfin] at hi

      have hlt_half : NumberField.HeightOneSpectrum.adicAbv K v (x - algebraMap (𝓞 K) K r) < 1 / 2 := by
        exact lt_of_lt_of_le hi (min_le_left _ _)

      have halg_r_val : v.valuation K (algebraMap (𝓞 K) K r) = 1 := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
          (unit_mod_ideal_not_in_prime
            (le_trans (finset_prod_ideal_le_factor S_fin _ v hvmem) (Ideal.pow_le_self hv))
            v.isPrime.ne_top hr_unit)
      have halg_r_abv : NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K r) = 1 := by
        rw [NumberField.HeightOneSpectrum.adicAbv_def]
        have hne0 := NumberField.HeightOneSpectrum.absNorm_ne_zero (R := 𝓞 K) v
        have hne1 := ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (R := 𝓞 K) v)
        have := (WithZeroMulInt.toNNReal_eq_one_iff _ hne0 hne1).mpr halg_r_val
        exact_mod_cast this
      have hlt1 : NumberField.HeightOneSpectrum.adicAbv K v (x - algebraMap (𝓞 K) K r) < 1 := by
        linarith
      have hlt_r : NumberField.HeightOneSpectrum.adicAbv K v (x - algebraMap (𝓞 K) K r) <
          NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K r) := by
        rw [halg_r_abv]; exact hlt1
      have hna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
      have hmax := IsNonarchimedean.add_eq_max_of_ne hna hlt_r.ne
      rw [sub_add_cancel] at hmax
      have hxeq : NumberField.HeightOneSpectrum.adicAbv K v x = 1 := by
        rw [hmax, halg_r_abv, max_eq_right (le_of_lt hlt1)]
      have hne0 := NumberField.HeightOneSpectrum.absNorm_ne_zero (R := 𝓞 K) v
      have hne1 := ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (R := 𝓞 K) v)
      rw [NumberField.HeightOneSpectrum.adicAbv_def] at hxeq
      have hnnr : WithZeroMulInt.toNNReal hne0 (v.valuation K x) = 1 := by exact_mod_cast hxeq
      exact (WithZeroMulInt.toNNReal_eq_one_iff _ hne0 hne1).mp hnnr

    let x_unit : Kˣ := Units.mk0 x hx_ne
    have hx_mem : (x_unit : Kˣ) ∈ UnitsCoprime_subgroup' K 𝔪 := by
      intro v hv; simp only [Units.val_mk0, x_unit]; exact hx_coprime v hv
    let α_x : UnitsCoprime_subgroup' K 𝔪 := ⟨x_unit, hx_mem⟩

    have hsign_x : signMapHom K 𝔪 α_x = 1 := by
      funext ⟨w, hw⟩
      simp only [Pi.one_apply, signMapHom, signAtPlace]
      have hwmem : w ∈ S_inf' := Finset.mem_union_left _ hw
      have hi := hx (.inr ⟨w, hwmem⟩)
      simp only [target, absVals, ε] at hi
      have hw_real := 𝔪.infSupportFinset_isReal hw
      have him := embedding_im_zero hw_real x
      have hw_val_eq : w.val (x - 1) = ‖w.embedding (x - 1)‖ :=
        (NumberField.InfinitePlace.norm_embedding_eq w (x - 1)).symm
      have norm_eq : ‖w.embedding (x - 1)‖ = |((w.embedding (x - 1)).re)| := by
        have hze : (w.embedding (x - 1)) = ↑(w.embedding (x - 1)).re :=
          Complex.ext rfl (by simp [embedding_im_zero hw_real])
        rw [hze, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
      rw [hw_val_eq, norm_eq] at hi
      rw [map_sub, Complex.sub_re, map_one, Complex.one_re, abs_lt] at hi
      have hpos : 0 < (w.embedding (x : K)).re := by linarith [hi.1]
      show Multiplicative.ofAdd (if 0 < (w.embedding x).re then (0 : ZMod 2) else 1) = 1
      rw [if_pos hpos]
      rfl


    have hfp_x : finitePartMapHom K 𝔪 α_x = u := by


      have hprod : α_x = α_x * α₀⁻¹ * α₀ := by group
      rw [hprod, map_mul, hfp_α₀]
      suffices finitePartMapHom K 𝔪 (α_x * α₀⁻¹) = 1 by rw [this, one_mul]
      rw [finitePartMapHom_ker_iff]
      intro v hv


      have hvmem : v ∈ S_fin := by
        simp only [S_fin, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]; exact hv
      have hi := hx (.inl ⟨v, hvmem⟩)
      simp only [target, absVals, FinitePlace.toAbsoluteValue, ε, εfin] at hi

      have hval_quot : ((α_x * α₀⁻¹ : UnitsCoprime_subgroup' K 𝔪) : Kˣ) =
          x_unit * α_r⁻¹ := by
        simp [α_x, α₀, Subgroup.coe_mul, Subgroup.coe_inv]
      have hval_K : (((α_x * α₀⁻¹ : UnitsCoprime_subgroup' K 𝔪) : Kˣ) : K) =
          x * (algebraMap (𝓞 K) K r)⁻¹ := by
        rw [hval_quot]; simp [Units.val_mul, Units.val_inv_eq_inv_val, x_unit, α_r]
      rw [hval_K]

      have hsub_eq : x * (algebraMap (𝓞 K) K r)⁻¹ - 1 =
          (x - algebraMap (𝓞 K) K r) * (algebraMap (𝓞 K) K r)⁻¹ := by
        rw [sub_mul, mul_inv_cancel₀ halg_ne]
      rw [hsub_eq, Valuation.map_mul, Valuation.map_inv]

      have halg_r_val : v.valuation K (algebraMap (𝓞 K) K r) = 1 := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
          (unit_mod_ideal_not_in_prime
            (le_trans (finset_prod_ideal_le_factor S_fin _ v hvmem) (Ideal.pow_le_self hv))
            v.isPrime.ne_top hr_unit)
      rw [halg_r_val, inv_one, mul_one]


      have hlt_thresh : NumberField.HeightOneSpectrum.adicAbv K v
          (x - algebraMap (𝓞 K) K r) <
          ((Ideal.absNorm v.asIdeal : ℝ) ^
            (-(𝔪 (Place.finite v) - 1 : ℤ))) := by
        exact lt_of_lt_of_le hi (min_le_right _ _)


      have hne0 := NumberField.HeightOneSpectrum.absNorm_ne_zero (R := 𝓞 K) v
      have hne1 := ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (R := 𝓞 K) v)

      rw [NumberField.HeightOneSpectrum.adicAbv_def] at hlt_thresh


      set n := 𝔪 (Place.finite v) with hn_def
      set val_y := v.valuation K (x - algebraMap (𝓞 K) K r) with hval_y_def

      have htoNNReal_coe : WithZeroMulInt.toNNReal hne0
          (↑(Multiplicative.ofAdd (-(↑n - 1 : ℤ))) : WithZero (Multiplicative ℤ)) =
          (↑(Ideal.absNorm v.asIdeal) : NNReal) ^ (-(↑n - 1 : ℤ)) := by
        simp [WithZeroMulInt.toNNReal, WithZero.coe_ne_zero]

      have hrhs_cast : (↑(Ideal.absNorm v.asIdeal) : ℝ) ^ (-(↑n - 1 : ℤ)) =
          ↑((↑(Ideal.absNorm v.asIdeal) : NNReal) ^ (-(↑n - 1 : ℤ))) := by
        rw [NNReal.coe_zpow]; push_cast; ring
      rw [hrhs_cast] at hlt_thresh


      rw [← htoNNReal_coe] at hlt_thresh
      have hnnr_lt : WithZeroMulInt.toNNReal hne0 val_y <
          WithZeroMulInt.toNNReal hne0
            (↑(Multiplicative.ofAdd (-(↑n - 1 : ℤ)))) := by
        exact_mod_cast hlt_thresh

      have hlt_one := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (R := 𝓞 K) v
      have hval_lt : val_y < ↑(Multiplicative.ofAdd (-(↑n - 1 : ℤ))) :=
        (WithZeroMulInt.toNNReal_strictMono hlt_one).lt_iff_lt.mp hnnr_lt

      rcases val_y with _ | a
      ·
        exact WithZero.zero_le _
      ·
        show (a : WithZero (Multiplicative ℤ)) ≤ _
        have hval_lt' : (a : WithZero (Multiplicative ℤ)) <
            ↑(Multiplicative.ofAdd (-(↑n - 1 : ℤ))) := hval_lt
        rw [WithZero.coe_lt_coe] at hval_lt'
        rw [WithZero.coe_le_coe]
        have h_add : Multiplicative.toAdd a < -(↑n - 1 : ℤ) := by
          rwa [show a = Multiplicative.ofAdd (Multiplicative.toAdd a) from (ofAdd_toAdd a).symm,
            Multiplicative.ofAdd_lt] at hval_lt'
        rw [show a = Multiplicative.ofAdd (Multiplicative.toAdd a) from (ofAdd_toAdd a).symm]
        exact Multiplicative.ofAdd_le.mpr (by omega)
    exact ⟨α_x, hsign_x, hfp_x⟩

theorem finitePartMapHom_surj_on_ker_sign (𝔪 : @Modulus K _ _)
    (u : (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)ˣ) :
    ∃ α : UnitsCoprime_subgroup' K 𝔪,
      signMapHom K 𝔪 α = 1 ∧ finitePartMapHom K 𝔪 α = u := by
  exact weak_approx_coprime_sign_finitePart 𝔪 u

theorem signTimesFinitePart_surjective (𝔪 : @Modulus K _ _) :
    Function.Surjective
      (MonoidHom.prod (signMapHom K 𝔪) (finitePartMapHom K 𝔪)) := by
  intro ⟨s, u⟩

  obtain ⟨α₁, hα₁⟩ := signMapHom_surjective 𝔪 s

  obtain ⟨α₂, hα₂_sign, hα₂_fin⟩ :=
    finitePartMapHom_surj_on_ker_sign 𝔪 (u * (finitePartMapHom K 𝔪 α₁)⁻¹)

  refine ⟨α₁ * α₂, Prod.ext ?_ ?_⟩
  ·
    show ((signMapHom K 𝔪 (α₁ * α₂)), (finitePartMapHom K 𝔪 (α₁ * α₂))).1 = s
    simp only [map_mul, hα₁, hα₂_sign, mul_one]
  ·
    show ((signMapHom K 𝔪 (α₁ * α₂)), (finitePartMapHom K 𝔪 (α₁ * α₂))).2 = u
    simp only [map_mul, hα₂_fin]
    rw [mul_comm ((finitePartMapHom K 𝔪) α₁) (u * _), mul_assoc, inv_mul_cancel,
        mul_one]

theorem finite_part_map_exists (𝔪 : @Modulus K _ _) :
    ∃ (f : UnitsCoprime_subgroup' K 𝔪 →*
        (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)ˣ),
      (∀ α : UnitsCoprime_subgroup' K 𝔪,
        f α = 1 ↔
          ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
            v.valuation K (((α : Kˣ) : K) - 1) ≤
              ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ)))) ∧
      Function.Surjective (MonoidHom.prod (signMapHom K 𝔪) f) :=
  ⟨finitePartMapHom K 𝔪, finitePartMapHom_ker_iff 𝔪, signTimesFinitePart_surjective 𝔪⟩

theorem theorem_21_8_quotient_iso (𝔪 : @Modulus K _ _) :
    Nonempty (QuotientUnits K 𝔪 ≃* SignsTimesUnits K 𝔪) := by
  obtain ⟨f, hf_ker, hφ_surj⟩ := finite_part_map_exists 𝔪
  set φ := MonoidHom.prod (signMapHom K 𝔪) f

  have hker : φ.ker = UnitsCongruent_in_UnitsCoprime K 𝔪 := by
    rw [MonoidHom.ker_prod]
    ext ⟨α, hα_cop⟩
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker]
    constructor
    ·
      intro ⟨hsign, hfin⟩
      refine ⟨hα_cop, (hf_ker ⟨α, hα_cop⟩).mp hfin, ?_⟩
      intro w hw


      have : signMapHom K 𝔪 ⟨α, hα_cop⟩ = 1 := hsign
      have hw_mem : w ∈ 𝔪.infSupportFinset := by
        simp only [Modulus.infSupportFinset, Set.Finite.mem_toFinset,
          Set.mem_preimage, Set.mem_setOf_eq]
        exact hw
      have := congr_fun this ⟨w, hw_mem⟩
      simp only [signMapHom, MonoidHom.coe_mk, OneHom.coe_mk, Pi.one_apply] at this
      rw [ofAdd_eq_one] at this
      exact (signAtPlace_eq_zero_iff _ _).mp this
    ·
      intro ⟨_, hα_cong, hα_sign⟩
      refine ⟨?_, (hf_ker ⟨α, hα_cop⟩).mpr hα_cong⟩

      ext ⟨w, hw_mem⟩
      simp only [signMapHom, MonoidHom.coe_mk, OneHom.coe_mk, Pi.one_apply,
        toAdd_ofAdd, toAdd_one]

      exact (signAtPlace_eq_zero_iff _ _).mpr (hα_sign w (by
        simp only [Modulus.infSupportFinset, Set.Finite.mem_toFinset,
          Set.mem_preimage, Set.mem_setOf_eq] at hw_mem
        exact hw_mem))
  haveI : (UnitsCongruent_in_UnitsCoprime K 𝔪).Normal :=
    hker ▸ MonoidHom.normal_ker φ
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ_surj)⟩

instance instFintypeQuotientUnits (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Fintype (QuotientUnits K 𝔪) :=
  Fintype.ofEquiv _ (Classical.choice (theorem_21_8_quotient_iso 𝔪)).toEquiv.symm

noncomputable def instFintypeRayClassGroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Fintype (RayClassGroup K 𝔪) :=


  @Group.fintypeOfDomOfCoker (QuotientUnits K 𝔪) (RayClassGroup K 𝔪) _ _
    (instFintypeQuotientUnits K 𝔪) (exactSeq_map3 𝔪)
    (Subgroup.normal_of_comm _)
    (Fintype.ofEquiv (ClassGroup (NumberField.RingOfIntegers K))
      ((QuotientGroup.quotientKerEquivOfSurjective
        (exactSeq_map4 𝔪) (exactSeq_surjective 𝔪)).toEquiv.symm.trans
        (Subgroup.quotientEquivOfEq (exactSeq_exact_at_ray_class 𝔪).symm)))

attribute [instance] instFintypeRayClassGroup

theorem corollary_21_9_ray_class_number (𝔪 : @Modulus K _ _) :
    Nat.card (RayClassGroup K 𝔪) * (UnitsInCongruenceSubgroup_subgroup K 𝔪).index =
    Nat.card (SignsTimesUnits K 𝔪) *
      Nat.card (ClassGroup (NumberField.RingOfIntegers K)) := by


  have h_index_f2 : (exactSeq_map2 𝔪).ker.index = Nat.card (exactSeq_map2 𝔪).range := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (exactSeq_map2 𝔪)).toEquiv

  have h_ker2_eq_H : (exactSeq_map2 𝔪).ker = UnitsInCongruenceSubgroup_subgroup K 𝔪 := by
    rw [← exactSeq_exact_at_units 𝔪]
    exact (UnitsInCongruenceSubgroup_subgroup K 𝔪).range_subtype


  have h_ker3_eq_range2 : Nat.card (↥(exactSeq_map3 𝔪).ker) =
      Nat.card (↥(exactSeq_map2 𝔪).range) := by
    congr 1; rw [exactSeq_exact_at_quotient 𝔪]

  have h_lagrange_QU : Nat.card (↥(exactSeq_map3 𝔪).ker) * (exactSeq_map3 𝔪).ker.index =
      Nat.card (QuotientUnits K 𝔪) :=
    Subgroup.card_mul_index (exactSeq_map3 𝔪).ker

  have h_index_f3 : (exactSeq_map3 𝔪).ker.index = Nat.card (exactSeq_map3 𝔪).range := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (exactSeq_map3 𝔪)).toEquiv

  have h_lagrange_RCG : Nat.card (↥(exactSeq_map4 𝔪).ker) * (exactSeq_map4 𝔪).ker.index =
      Nat.card (RayClassGroup K 𝔪) :=
    Subgroup.card_mul_index (exactSeq_map4 𝔪).ker

  have h_ker4_eq_range3 : Nat.card (↥(exactSeq_map4 𝔪).ker) =
      Nat.card (↥(exactSeq_map3 𝔪).range) := by
    congr 1; rw [exactSeq_exact_at_ray_class 𝔪]

  have h_index_f4 : (exactSeq_map4 𝔪).ker.index =
      Nat.card (ClassGroup (NumberField.RingOfIntegers K)) := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective (exactSeq_map4 𝔪) (exactSeq_surjective 𝔪)).toEquiv

  have h_iso : Nat.card (QuotientUnits K 𝔪) = Nat.card (SignsTimesUnits K 𝔪) :=
    Nat.card_congr (Classical.choice (theorem_21_8_quotient_iso 𝔪)).toEquiv

  have h_RCG : Nat.card (RayClassGroup K 𝔪) =
      Nat.card (↥(exactSeq_map3 𝔪).range) * Nat.card (ClassGroup (NumberField.RingOfIntegers K)) := by
    rw [← h_lagrange_RCG, h_ker4_eq_range3, h_index_f4]

  have h_QU : Nat.card (QuotientUnits K 𝔪) =
      Nat.card (↥(exactSeq_map2 𝔪).range) * Nat.card (↥(exactSeq_map3 𝔪).range) := by
    rw [← h_lagrange_QU, h_ker3_eq_range2, h_index_f3]

  have h_STU : Nat.card (SignsTimesUnits K 𝔪) =
      Nat.card (↥(exactSeq_map2 𝔪).range) * Nat.card (↥(exactSeq_map3 𝔪).range) := by
    rw [← h_iso, h_QU]

  rw [h_RCG, ← h_ker2_eq_H, h_index_f2, h_STU]
  ring

theorem corollary_21_9_class_dvd_ray (𝔪 : @Modulus K _ _) :
    Fintype.card (ClassGroup (NumberField.RingOfIntegers K)) ∣
      Fintype.card (RayClassGroup K 𝔪) := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_dvd_of_surjective (exactSeq_map4 𝔪) (exactSeq_surjective 𝔪)

theorem corollary_21_9_ray_dvd (𝔪 : @Modulus K _ _) :
    Fintype.card (RayClassGroup K 𝔪) ∣
      Fintype.card (ClassGroup (NumberField.RingOfIntegers K)) *
        Fintype.card (SignsTimesUnits K 𝔪) := by
  simp only [← Nat.card_eq_fintype_card]

  have hcard_iso : Nat.card (QuotientUnits K 𝔪) = Nat.card (SignsTimesUnits K 𝔪) :=
    Nat.card_congr (Classical.choice (theorem_21_8_quotient_iso 𝔪)).toEquiv

  have h_card_eq : Nat.card (↥(exactSeq_map4 𝔪).ker) * (exactSeq_map4 𝔪).ker.index =
      Nat.card (RayClassGroup K 𝔪) := Subgroup.card_mul_index _

  have h_index : (exactSeq_map4 𝔪).ker.index =
      Nat.card (ClassGroup (NumberField.RingOfIntegers K)) := by
    rw [Subgroup.index]
    exact Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective (exactSeq_map4 𝔪) (exactSeq_surjective 𝔪)).toEquiv

  have h_range_dvd : Nat.card (↥(exactSeq_map3 𝔪).range) ∣ Nat.card (QuotientUnits K 𝔪) :=
    Subgroup.card_range_dvd (exactSeq_map3 𝔪)

  have h_ker_range : Nat.card (↥(exactSeq_map4 𝔪).ker) =
      Nat.card (↥(exactSeq_map3 𝔪).range) := by
    have : ↥(exactSeq_map4 𝔪).ker = ↥(exactSeq_map3 𝔪).range := by
      rw [exactSeq_exact_at_ray_class 𝔪]
    rw [this]

  rw [← h_card_eq, h_index, h_ker_range, mul_comm]
  exact mul_dvd_mul_left _ (h_range_dvd.trans (dvd_of_eq hcard_iso))

theorem corollary_21_9 (𝔪 : @Modulus K _ _) :
    (Nat.card (RayClassGroup K 𝔪) * (UnitsInCongruenceSubgroup_subgroup K 𝔪).index =
      Nat.card (SignsTimesUnits K 𝔪) *
        Nat.card (ClassGroup (NumberField.RingOfIntegers K))) ∧
    (Fintype.card (ClassGroup (NumberField.RingOfIntegers K)) ∣
      Fintype.card (RayClassGroup K 𝔪)) ∧
    (Fintype.card (RayClassGroup K 𝔪) ∣
      Fintype.card (ClassGroup (NumberField.RingOfIntegers K)) *
        Fintype.card (SignsTimesUnits K 𝔪)) :=
  ⟨corollary_21_9_ray_class_number 𝔪,
   corollary_21_9_class_dvd_ray 𝔪,
   corollary_21_9_ray_dvd 𝔪⟩

abbrev Prime' (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

noncomputable def partialDedekindZeta (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) : ℂ → ℂ := fun s =>
  ∏' (𝔭 : S), (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s))⁻¹

lemma eulerFactor_analyticAt_one {K : Type*} [Field K] [NumberField K]
    (𝔭 : Prime' K) :
    AnalyticAt ℂ (fun s : ℂ => (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))⁻¹) 1 := by
  have hne : (Ideal.absNorm 𝔭.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr ((Ideal.absNorm_ne_zero_iff _).mpr
      (𝔭.asIdeal.finiteQuotientOfFreeOfNeBot 𝔭.ne_bot))
  apply AnalyticAt.inv
  · apply AnalyticAt.sub analyticAt_const
    have hrw : ∀ s : ℂ, (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s) =
        Complex.exp (-s * Complex.log (Ideal.absNorm 𝔭.asIdeal : ℂ)) := by
      intro s; rw [Complex.cpow_def_of_ne_zero hne]; ring_nf
    simp_rw [hrw]
    exact ((analyticAt_id (𝕜 := ℂ)).neg.mul analyticAt_const).cexp
  · rw [sub_ne_zero]; intro h
    rw [show (-(1 : ℂ)) = ((-1 : ℤ) : ℂ) from by push_cast; ring,
        Complex.cpow_intCast, zpow_neg_one] at h
    have h3 : Ideal.absNorm 𝔭.asIdeal = 1 := by exact_mod_cast (inv_eq_one.mp h.symm)
    have hmax := IsDedekindDomain.HeightOneSpectrum.isMaximal 𝔭
    haveI := 𝔭.asIdeal.finiteQuotientOfFreeOfNeBot 𝔭.ne_bot
    haveI : Fintype (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
    haveI := (Ideal.Quotient.nontrivial_iff (I := 𝔭.asIdeal)).mpr hmax.ne_top
    have h5 : 1 < Fintype.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) :=
      Fintype.one_lt_card
    have h6 : Ideal.absNorm 𝔭.asIdeal =
        Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := rfl
    rw [h6, Nat.card_eq_fintype_card] at h3
    linarith











def HasMeromorphicContinuationWithPoleOrder (f : ℂ → ℂ) (m : ℤ) : Prop :=
  MeromorphicAt f 1 ∧ meromorphicOrderAt f 1 = ↑(-m)


def HasPolarDensity (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) (ρ : ℚ) : Prop :=
  ∃ (n : ℕ+) (m : ℤ),
    HasMeromorphicContinuationWithPoleOrder (partialDedekindZeta K S ^ (n : ℕ)) m ∧
    (ρ : ℚ) = (m : ℚ) / (n : ℚ)

def HasDirichletDensity (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) (ρ : ℚ) : Prop :=
  Filter.Tendsto (fun s : ℝ =>
    (∑' (𝔭 : S), ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) /
    Real.log (1 / (s - 1)))
    (nhdsWithin 1 (Set.Ioi 1)) (nhds (ρ : ℝ))

def HasNaturalDensity (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) (ρ : ℚ) : Prop :=
  Filter.Tendsto (fun x : ℝ =>
    (Set.ncard {𝔭 : Prime' K | 𝔭 ∈ S ∧ (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x} : ℝ) /
    (Set.ncard {𝔭 : Prime' K | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x} : ℝ))
    Filter.atTop (nhds (ρ : ℝ))


theorem hasDirichletDensity_unique {K : Type*} [Field K] [NumberField K]
    {S : Set (Prime' K)} {ρ₁ ρ₂ : ℚ}
    (h₁ : HasDirichletDensity K S ρ₁) (h₂ : HasDirichletDensity K S ρ₂) : ρ₁ = ρ₂ := by
  exact_mod_cast tendsto_nhds_unique h₁ h₂

theorem hasNaturalDensity_unique {K : Type*} [Field K] [NumberField K]
    {S : Set (Prime' K)} {ρ₁ ρ₂ : ℚ}
    (h₁ : HasNaturalDensity K S ρ₁) (h₂ : HasNaturalDensity K S ρ₂) : ρ₁ = ρ₂ := by
  exact_mod_cast tendsto_nhds_unique h₁ h₂

theorem meromorphic_poleOrder_realLog_limit
    (f : ℂ → ℂ) (m : ℤ)
    (hm : HasMeromorphicContinuationWithPoleOrder f m) :
    ∃ C : ℝ, Filter.Tendsto (fun s : ℝ =>
      Real.log ‖f ((s : ℂ))‖ + (m : ℝ) * Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds C) := by
  obtain ⟨hmer, hord⟩ := hm
  rw [meromorphicOrderAt_eq_int_iff hmer] at hord
  obtain ⟨g, hg_an, hg_ne, hf_eq⟩ := hord
  refine ⟨Real.log ‖g 1‖, ?_⟩

  have hg_lim : Filter.Tendsto (fun s : ℝ => Real.log ‖g ((s : ℂ))‖)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log ‖g 1‖)) := by
    have h_gR : ContinuousAt (fun s : ℝ => g ((s : ℂ))) 1 :=
      hg_an.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
    exact ((continuous_norm.continuousAt.comp h_gR).log (by simp [hg_ne])).continuousWithinAt.tendsto

  apply Filter.Tendsto.congr'
  ·
    have hf_eq_R : ∀ᶠ (s : ℝ) in nhdsWithin 1 (Set.Ioi 1),
        f (↑s) = ((↑s - 1 : ℂ)) ^ (-m) • g (↑s) := by
      rw [Filter.Eventually, mem_nhdsWithin] at hf_eq ⊢
      obtain ⟨U, hU_open, h1U, hUprop⟩ := hf_eq
      refine ⟨Complex.ofReal ⁻¹' U, hU_open.preimage Complex.continuous_ofReal,
        by simp [h1U], ?_⟩
      intro s ⟨hsU, hs_ioi⟩
      exact hUprop ⟨hsU, by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact fun h => absurd (Complex.ofReal_injective h) (ne_of_gt hs_ioi)⟩
    have hg_ne_R : ∀ᶠ (s : ℝ) in nhdsWithin 1 (Set.Ioi 1), g (↑s) ≠ 0 := by
      have h_gR : ContinuousAt (fun s : ℝ => g ((s : ℂ))) 1 :=
        hg_an.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
      have : (fun s : ℝ => g ((s : ℂ))) 1 = g 1 := by simp
      exact (h_gR.eventually (this ▸ isOpen_ne.mem_nhds hg_ne)).filter_mono nhdsWithin_le_nhds
    show (fun s : ℝ => Real.log ‖g ((s : ℂ))‖) =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
        (fun s : ℝ => Real.log ‖f ((s : ℂ))‖ + (m : ℝ) * Real.log (s - 1))
    filter_upwards [hf_eq_R, hg_ne_R,
      eventually_nhdsWithin_of_forall (fun s (hs : s ∈ Set.Ioi 1) => hs)]
      with s hf_s hg_s hs1
    have hs1' : 1 < s := hs1
    rw [hf_s, norm_smul, norm_zpow]
    have hs1_eq : ‖(↑s - 1 : ℂ)‖ = s - 1 := by
      rw [show (↑s - 1 : ℂ) = ↑(s - 1) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hs1_eq]
    have hs1_pos : (0 : ℝ) < s - 1 := by linarith
    rw [Real.log_mul (zpow_ne_zero _ (ne_of_gt hs1_pos)) (norm_ne_zero_iff.mpr hg_s)]
    rw [Real.log_zpow]
    push_cast; ring
  · exact hg_lim

instance instFiniteIdealNorm' (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOf_absNorm_eq n).to_subtype

instance instFinitePrimesNorm' (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finite {𝔭 : Prime' K // Ideal.absNorm 𝔭.asIdeal = n} :=
  Finite.of_injective
    (fun ⟨𝔭, h⟩ => (⟨𝔭.asIdeal, h⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
    (fun ⟨a, _⟩ ⟨b, _⟩ h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext h))

lemma card_primes_le_card_ideals' (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Nat.card {𝔭 : Prime' K // Ideal.absNorm 𝔭.asIdeal = n} ≤
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  Nat.card_le_card_of_injective
    (fun ⟨𝔭, h⟩ => (⟨𝔭.asIdeal, h⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
    (fun ⟨a, _⟩ ⟨b, _⟩ h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext h))

set_option maxHeartbeats 800000 in
lemma ideal_count_rpow_summable' (K : Type*) [Field K] [NumberField K]
    (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) *
      ((n : ℝ) ^ (-σ))) := by
  have hLS : LSeriesSummable
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) (σ : ℂ) := by
    apply LSeriesSummable_of_sum_norm_bigO_and_nonneg _ (fun n => Nat.cast_nonneg _) zero_le_one
    · simp; exact hσ
    apply Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (𝕜 := ℝ)
      (a := NumberField.dedekindZeta_residue K)
    simp only [Real.rpow_one]
    refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
      tendsto_natCast_atTop_atTop).congr fun n => ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]; congr 1; norm_cast
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ => Ideal.finite_setOf_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  exact (hLS.norm).of_nonneg_of_le (fun n => by positivity) (fun n => by
    rw [LSeries.norm_term_eq]; split_ifs with h
    · subst h
      simp [Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt (by linarith : (0 : ℝ) < σ)))]
    · rw [Complex.norm_natCast, Complex.ofReal_re, div_eq_mul_inv,
        ← Real.rpow_neg (Nat.cast_nonneg n)])

set_option maxHeartbeats 400000 in
lemma summable_primeIdeal_absNorm_rpow'
    (K : Type*) [Field K] [NumberField K] (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun 𝔭 : Prime' K => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-σ)) := by
  rw [← (Equiv.sigmaFiberEquiv (fun 𝔭 : Prime' K =>
    Ideal.absNorm 𝔭.asIdeal)).summable_iff]
  suffices h : Summable (fun p : (n : ℕ) × {𝔭 : Prime' K //
      Ideal.absNorm 𝔭.asIdeal = n} => ((p.1 : ℝ) ^ (-σ))) by
    exact h.congr (fun ⟨n, 𝔭, h⟩ => by
      simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply]
      congr 1; exact_mod_cast h.symm)
  rw [summable_sigma_of_nonneg (fun ⟨n, _⟩ => by positivity)]
  exact ⟨fun n => Summable.of_finite, by
    simp_rw [tsum_const, nsmul_eq_mul]
    exact Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_primes_le_card_ideals' K n) (by positivity))
      (ideal_count_rpow_summable' K σ hσ)⟩

private lemma norm_inv_one_sub_sub_one {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    ‖(1 - a)⁻¹ - 1‖ ≤ 2 * ‖a‖ := by
  by_cases ha0 : a = 0; · simp [ha0]
  have ha1 : ‖a‖ < 1 := by linarith
  have h1a : (1 : ℂ) - a ≠ 0 := by
    intro h; have := sub_eq_zero.mp h; rw [← this] at ha1; simp at ha1
  rw [show (1 - a)⁻¹ - 1 = a * (1 - a)⁻¹ from by field_simp; ring,
      norm_mul, norm_inv]
  calc ‖a‖ * ‖(1 : ℂ) - a‖⁻¹
      ≤ ‖a‖ * (1 - ‖a‖)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (inv_anti₀ (by linarith)
            (by linarith [norm_sub_norm_le (1 : ℂ) a, norm_one (α := ℂ)]))
          (norm_nonneg a)
    _ ≤ ‖a‖ * (1 / 2)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (inv_anti₀ (by linarith : (0 : ℝ) < 1 / 2) (by linarith)) (norm_nonneg a)
    _ = 2 * ‖a‖ := by ring

set_option maxHeartbeats 400000 in
theorem partialDedekindZeta_multipliable
    {K : Type*} [Field K] [NumberField K]
    (S : Set (Prime' K)) (s : ℂ) (hs : 1 < s.re) :
    Multipliable (fun (𝔭 : S) =>
      (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s))⁻¹) := by

  have key : (fun (𝔭 : S) =>
      (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s))⁻¹) =
    (fun (𝔭 : S) => 1 + ((1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s))⁻¹ - 1)) := by
    ext; ring
  rw [key]
  apply Complex.multipliable_one_add_of_summable
  apply Summable.of_norm
  have hre : (-s).re ≠ 0 := by simp; linarith

  let g : S → ℝ := fun 𝔭 => 2 * (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s.re)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (f := g)
  · intro ⟨𝔭, h𝔭⟩
    set a := (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)
    have hN : 2 ≤ Ideal.absNorm 𝔭.asIdeal :=
      NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭
    have h_cpow_norm : ‖(↑(Ideal.absNorm 𝔭.asIdeal) : ℂ) ^ (-s)‖ =
        (↑(Ideal.absNorm 𝔭.asIdeal) : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_re_ne_zero _ hre, Complex.neg_re]
    have h_cpow_le : (↑(Ideal.absNorm 𝔭.asIdeal) : ℝ) ^ (-s.re) ≤ 1 / 2 := by
      calc (↑(Ideal.absNorm 𝔭.asIdeal) : ℝ) ^ (-s.re)
          ≤ (2 : ℝ) ^ (-s.re) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hN) (by linarith)
        _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
        _ = 1 / 2 := by norm_num
    have ha_norm : ‖a‖ ≤ 1 / 2 := by rw [h_cpow_norm]; exact h_cpow_le
    show ‖(1 - (Ideal.absNorm (⟨𝔭, h𝔭⟩ : S).1.asIdeal : ℂ) ^ (-s))⁻¹ - 1‖ ≤ g ⟨𝔭, h𝔭⟩
    show ‖(1 - a)⁻¹ - 1‖ ≤ 2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s.re)
    calc ‖(1 - a)⁻¹ - 1‖
        ≤ 2 * ‖a‖ := norm_inv_one_sub_sub_one ha_norm
      _ = 2 * (↑(Ideal.absNorm 𝔭.asIdeal) : ℝ) ^ (-s.re) := by rw [h_cpow_norm]
  · show Summable g
    exact ((summable_primeIdeal_absNorm_rpow' K s.re hs).subtype S).mul_left 2

theorem partialDedekindZeta_log_norm_eq_tsum
    {K : Type*} [Field K] [NumberField K]
    (S : Set (Prime' K)) {s : ℝ} (hs : 1 < s) :
    Real.log ‖partialDedekindZeta K S ((s : ℂ))‖ =
    ∑' (𝔭 : S), -Real.log (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s)) ∧
    Summable (fun (𝔭 : S) =>
      -Real.log (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) ∧
    Summable (fun (𝔭 : S) =>
      (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s)) := by

  set N : S → ℕ := fun 𝔭 => Ideal.absNorm (𝔭 : Prime' K).asIdeal with hN_def

  have hN_ge : ∀ 𝔭 : S, 2 ≤ N 𝔭 := fun 𝔭 =>
    NumberField.HeightOneSpectrum.one_lt_absNorm (𝔭 : Prime' K)

  have h_sum_rpow : Summable (fun 𝔭 : S => (N 𝔭 : ℝ) ^ (-s)) :=
    (summable_primeIdeal_absNorm_rpow' K s hs).subtype S

  have hN_pos : ∀ 𝔭 : S, (0 : ℝ) < (N 𝔭 : ℝ) := fun 𝔭 => by
    have := hN_ge 𝔭; exact_mod_cast (show 0 < N 𝔭 by omega)
  have h_rpow_pos : ∀ 𝔭 : S, 0 < (N 𝔭 : ℝ) ^ (-s) := fun 𝔭 => by
    exact Real.rpow_pos_of_pos (hN_pos 𝔭) (-s)
  have h_rpow_le_half : ∀ 𝔭 : S, (N 𝔭 : ℝ) ^ (-s) ≤ 1 / 2 := fun 𝔭 => by
    calc (N 𝔭 : ℝ) ^ (-s)
        ≤ (2 : ℝ) ^ (-s) := by
          apply Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hN_ge 𝔭) (by linarith)
      _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
      _ = 1 / 2 := by norm_num
  have h_rpow_lt_one : ∀ 𝔭 : S, (N 𝔭 : ℝ) ^ (-s) < 1 := fun 𝔭 =>
    lt_of_le_of_lt (h_rpow_le_half 𝔭) (by norm_num)

  have h_one_sub_pos : ∀ 𝔭 : S, 0 < 1 - (N 𝔭 : ℝ) ^ (-s) := fun 𝔭 => by linarith [h_rpow_lt_one 𝔭]

  have h_inv_pos : ∀ 𝔭 : S, 0 < (1 - (N 𝔭 : ℝ) ^ (-s))⁻¹ := fun 𝔭 =>
    inv_pos.mpr (h_one_sub_pos 𝔭)

  have h_cpow_eq : ∀ 𝔭 : S, (N 𝔭 : ℂ) ^ (-(↑s : ℂ)) = ↑((N 𝔭 : ℝ) ^ (-s)) := fun 𝔭 => by
    rw [show (-(↑s : ℂ)) = (((-s) : ℝ) : ℂ) from by push_cast; ring]
    rw [show (N 𝔭 : ℂ) = ((N 𝔭 : ℝ) : ℂ) from by push_cast; ring]
    exact (Complex.ofReal_cpow (Nat.cast_nonneg (N 𝔭)) (-s)).symm

  have h_factor_eq : ∀ 𝔭 : S,
      (1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹ = ↑((1 - (N 𝔭 : ℝ) ^ (-s))⁻¹) := fun 𝔭 => by
    rw [h_cpow_eq]
    push_cast
    ring

  have h_norm_factor : ∀ 𝔭 : S,
      ‖(1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹‖ = (1 - (N 𝔭 : ℝ) ^ (-s))⁻¹ := fun 𝔭 => by
    rw [h_factor_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (h_inv_pos 𝔭)]

  have h_sum_neg : Summable (fun 𝔭 : S => -(N 𝔭 : ℝ) ^ (-s)) := h_sum_rpow.neg
  have h_sum_log : Summable (fun 𝔭 : S => Real.log (1 + -(N 𝔭 : ℝ) ^ (-s))) :=
    Real.summable_log_one_add_of_summable h_sum_neg

  have h_sum_log' : Summable (fun 𝔭 : S => Real.log (1 - (N 𝔭 : ℝ) ^ (-s))) :=
    h_sum_log.congr (fun 𝔭 => by ring_nf)

  have h_sum_neg_log : Summable (fun 𝔭 : S =>
      -Real.log (1 - (N 𝔭 : ℝ) ^ (-s))) := h_sum_log'.neg

  have h_sum_log_inv : Summable (fun 𝔭 : S =>
      Real.log ((1 - (N 𝔭 : ℝ) ^ (-s))⁻¹)) := by
    refine h_sum_neg_log.congr (fun 𝔭 => ?_)
    rw [Real.log_inv]

  have h_mult : Multipliable (fun 𝔭 : S =>
      (1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹) := by
    have hre : (1 : ℝ) < ((↑s : ℂ)).re := by simp [hs]
    exact partialDedekindZeta_multipliable S (↑s) hre

  have h_norm_tprod : ‖∏' 𝔭 : S, (1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹‖ =
      ∏' 𝔭 : S, ‖(1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹‖ := h_mult.norm_tprod

  have h_tprod_norm_eq : ∏' 𝔭 : S, ‖(1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹‖ =
      ∏' 𝔭 : S, (1 - (N 𝔭 : ℝ) ^ (-s))⁻¹ := tprod_congr (fun 𝔭 => h_norm_factor 𝔭)

  have h_exp_eq : Real.exp (∑' 𝔭 : S, Real.log ((1 - (N 𝔭 : ℝ) ^ (-s))⁻¹)) =
      ∏' 𝔭 : S, (1 - (N 𝔭 : ℝ) ^ (-s))⁻¹ :=
    Real.rexp_tsum_eq_tprod h_inv_pos h_sum_log_inv

  have h_log_tprod : Real.log (∏' 𝔭 : S, (1 - (N 𝔭 : ℝ) ^ (-s))⁻¹) =
      ∑' 𝔭 : S, Real.log ((1 - (N 𝔭 : ℝ) ^ (-s))⁻¹) := by
    rw [← h_exp_eq, Real.log_exp]

  have h_log_inv_eq : ∀ 𝔭 : S,
      Real.log ((1 - (N 𝔭 : ℝ) ^ (-s))⁻¹) = -Real.log (1 - (N 𝔭 : ℝ) ^ (-s)) := fun 𝔭 =>
    Real.log_inv (1 - (N 𝔭 : ℝ) ^ (-s))

  have h_main : Real.log ‖partialDedekindZeta K S ((s : ℂ))‖ =
      ∑' 𝔭 : S, -Real.log (1 - (N 𝔭 : ℝ) ^ (-s)) := by
    show Real.log ‖∏' 𝔭 : S, (1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹‖ = _
    rw [h_norm_tprod, h_tprod_norm_eq, h_log_tprod]
    exact tsum_congr h_log_inv_eq
  exact ⟨h_main, h_sum_neg_log, h_sum_rpow⟩

instance instFiniteIdealNorm_rl (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOf_absNorm_eq n).to_subtype

instance instFinitePrimesNorm_rl (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finite {𝔭 : Prime' K // Ideal.absNorm 𝔭.asIdeal = n} :=
  Finite.of_injective
    (fun ⟨𝔭, h⟩ => (⟨𝔭.asIdeal, h⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
    (fun ⟨a, _⟩ ⟨b, _⟩ h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext h))

lemma card_primes_le_card_ideals_rl (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Nat.card {𝔭 : Prime' K // Ideal.absNorm 𝔭.asIdeal = n} ≤
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  Nat.card_le_card_of_injective
    (fun ⟨𝔭, h⟩ => (⟨𝔭.asIdeal, h⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
    (fun ⟨a, _⟩ ⟨b, _⟩ h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext h))

set_option maxHeartbeats 800000 in
lemma ideal_count_rpow_summable_rl (K : Type*) [Field K] [NumberField K]
    (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) *
      ((n : ℝ) ^ (-σ))) := by
  have hLS : LSeriesSummable
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) (σ : ℂ) := by
    apply LSeriesSummable_of_sum_norm_bigO_and_nonneg _ (fun n => Nat.cast_nonneg _) zero_le_one
    · simp; exact hσ
    apply Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (𝕜 := ℝ)
      (a := NumberField.dedekindZeta_residue K)
    simp only [Real.rpow_one]
    refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
      tendsto_natCast_atTop_atTop).congr fun n => ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]; congr 1; norm_cast
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ => Ideal.finite_setOf_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  exact (hLS.norm).of_nonneg_of_le (fun n => by positivity) (fun n => by
    rw [LSeries.norm_term_eq]; split_ifs with h
    · subst h
      simp [Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt (by linarith : (0 : ℝ) < σ)))]
    · rw [Complex.norm_natCast, Complex.ofReal_re, div_eq_mul_inv,
        ← Real.rpow_neg (Nat.cast_nonneg n)])

set_option maxHeartbeats 400000 in
lemma summable_primeIdeal_absNorm_rpow_rl
    (K : Type*) [Field K] [NumberField K] (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun 𝔭 : Prime' K => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-σ)) := by
  rw [← (Equiv.sigmaFiberEquiv (fun 𝔭 : Prime' K =>
    Ideal.absNorm 𝔭.asIdeal)).summable_iff]
  suffices h : Summable (fun p : (n : ℕ) × {𝔭 : Prime' K //
      Ideal.absNorm 𝔭.asIdeal = n} => ((p.1 : ℝ) ^ (-σ))) by
    exact h.congr (fun ⟨n, 𝔭, h⟩ => by
      simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply]
      congr 1; exact_mod_cast h.symm)
  rw [summable_sigma_of_nonneg (fun ⟨n, _⟩ => by positivity)]
  exact ⟨fun n => Summable.of_finite, by
    simp_rw [tsum_const, nsmul_eq_mul]
    exact Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_primes_le_card_ideals_rl K n) (by positivity))
      (ideal_count_rpow_summable_rl K σ hσ)⟩

theorem partialDedekindZeta_eulerProductLog_remainder_limit
    {K : Type*} [Field K] [NumberField K]
    (S : Set (Prime' K)) :
    ∃ C : ℝ, Filter.Tendsto (fun s : ℝ =>
      ∑' (𝔭 : S), (-Real.log (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s)) -
                    (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds C) := by

  set f : S → ℝ → ℝ := fun 𝔭 s =>
    -Real.log (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s)) -
    (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s) with hf_def

  set u : S → ℝ := fun 𝔭 => 2 * (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ ((-2 : ℝ))
    with hu_def

  have hN : ∀ 𝔭 : S, (2 : ℝ) ≤ (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) := by
    intro ⟨𝔭, _⟩
    have h1 := 𝔭.ne_bot
    have h2 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := by rwa [ne_eq, Ideal.absNorm_eq_zero_iff]
    have h3 : Ideal.absNorm 𝔭.asIdeal ≠ 1 := by
      intro h; exact 𝔭.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    exact_mod_cast (show 1 < Ideal.absNorm 𝔭.asIdeal by omega)

  have h_cont_each : ∀ 𝔭 : S, ContinuousOn (f 𝔭) (Set.Ici 1) := by
    intro 𝔭
    have hN𝔭 := hN 𝔭
    have hN_pos : (0 : ℝ) < (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) := by positivity
    apply ContinuousOn.sub
    · apply ContinuousOn.neg
      apply ContinuousOn.log
      · apply ContinuousOn.sub continuousOn_const
        exact (continuous_const.rpow continuous_neg
          (fun _ => Or.inl hN_pos.ne')).continuousOn
      · intro s hs
        simp only [Set.mem_Ici] at hs
        have : (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s) ≤ 1 / 2 := by
          rw [Real.rpow_neg hN_pos.le, one_div]
          gcongr
          calc (2 : ℝ) ≤ _ := hN𝔭
            _ = _ ^ (1 : ℝ) := by simp
            _ ≤ _ ^ s := Real.rpow_le_rpow_of_exponent_le (by linarith) hs
        linarith
    · exact (continuous_const.rpow continuous_neg
        (fun _ => Or.inl hN_pos.ne')).continuousOn

  have h_summable : Summable u := by
    have h_all := summable_primeIdeal_absNorm_rpow_rl K 2 (by norm_num : (1 : ℝ) < 2)
    have h_sub := h_all.subtype S
    exact (h_sub.const_smul 2).congr fun 𝔭 => by simp [u, Function.comp]

  have h_bound : ∀ 𝔭 : S, ∀ s ∈ Set.Ici (1 : ℝ), ‖f 𝔭 s‖ ≤ u 𝔭 := by
    intro 𝔭 s hs
    simp only [Set.mem_Ici] at hs
    have hN𝔭 := hN 𝔭
    set N := (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) with hN_def
    show ‖f 𝔭 s‖ ≤ u 𝔭
    simp only [hf_def, hu_def]
    rw [Real.norm_eq_abs]
    have hN0 : (0 : ℝ) ≤ N := by linarith
    have hx0 : 0 ≤ N ^ (-s) := by positivity
    have hx_half : N ^ (-s) ≤ 1 / 2 := by
      rw [Real.rpow_neg hN0, one_div]
      gcongr
      calc (2 : ℝ) ≤ N := hN𝔭
        _ = N ^ (1 : ℝ) := by simp
        _ ≤ N ^ s := Real.rpow_le_rpow_of_exponent_le (by linarith) hs
    have hx1 : N ^ (-s) < 1 := by linarith

    have hab : |N ^ (-s)| < 1 := by rwa [abs_of_nonneg hx0]
    have h1 := Real.abs_log_sub_add_sum_range_le hab 1
    simp only [Finset.range_one, Finset.sum_singleton, abs_of_nonneg hx0] at h1
    rw [show -(Real.log (1 - N ^ (-s))) - N ^ (-s) =
        -(N ^ (-s) + Real.log (1 - N ^ (-s))) from by ring, abs_neg]

    calc |N ^ (-s) + Real.log (1 - N ^ (-s))|
        ≤ (N ^ (-s)) ^ (1 + 1) / (1 - N ^ (-s)) := by
          convert h1 using 2
          simp [pow_succ, pow_zero]
      _ ≤ 2 * (N ^ (-s)) ^ 2 := by
          rw [show (1 : ℕ) + 1 = 2 from rfl]
          rw [div_le_iff₀ (by linarith)]; nlinarith
      _ = 2 * N ^ (-2 * s) := by
          rw [← Real.rpow_natCast (N ^ (-s)) 2, ← Real.rpow_mul hN0]; ring_nf
      _ ≤ 2 * N ^ ((-2 : ℝ)) := by
          gcongr
          · linarith
          · nlinarith

  have h_cont := continuousOn_tsum h_cont_each h_summable h_bound
  have h1_mem : (1 : ℝ) ∈ Set.Ici (1 : ℝ) := Set.self_mem_Ici
  exact ⟨_, (h_cont.continuousWithinAt h1_mem).tendsto.mono_left
    (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)⟩

theorem partialDedekindZeta_eulerProductLog
    {K : Type*} [Field K] [NumberField K]
    (S : Set (Prime' K)) :
    ∃ C : ℝ, Filter.Tendsto (fun s : ℝ =>
      Real.log ‖partialDedekindZeta K S ((s : ℂ))‖ -
      ∑' (𝔭 : S), ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds C) := by

  obtain ⟨C, hC⟩ := partialDedekindZeta_eulerProductLog_remainder_limit S
  refine ⟨C, ?_⟩


  refine hC.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  obtain ⟨h_eq, h_summable, h_summable_norm⟩ := partialDedekindZeta_log_norm_eq_tsum S hs
  rw [h_eq, h_summable.tsum_sub h_summable_norm]

theorem eulerProduct_log_asymptotic
    {K : Type*} [Field K] [NumberField K]
    {S : Set (Prime' K)} {n : ℕ+} {m : ℤ}
    (hm : HasMeromorphicContinuationWithPoleOrder
             (partialDedekindZeta K S ^ (n : ℕ)) m) :
    ∃ C : ℝ, Filter.Tendsto (fun s : ℝ =>
      (n : ℝ) * (∑' (𝔭 : S), ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) -
      (m : ℝ) * Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds C) := by

  obtain ⟨C₁, hC₁⟩ := meromorphic_poleOrder_realLog_limit _ m hm

  obtain ⟨C₂, hC₂⟩ := partialDedekindZeta_eulerProductLog S

  set D : ℝ → ℝ := fun s =>
    ∑' (𝔭 : S), ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))
  set g : ℝ → ℝ := fun s => Real.log ‖partialDedekindZeta K S ((s : ℂ))‖

  have hC₁' : Filter.Tendsto (fun s : ℝ =>
      (n : ℝ) * g s + (m : ℝ) * Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds C₁) := by
    refine hC₁.congr (fun s => ?_)
    simp only [g, Pi.pow_apply, norm_pow, Real.log_pow]

  have hC₂' : Filter.Tendsto (fun s : ℝ =>
      (n : ℝ) * (g s - D s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((n : ℝ) * C₂)) :=
    hC₂.const_mul _

  have hMain : Filter.Tendsto (fun s : ℝ =>
      (n : ℝ) * D s + (m : ℝ) * Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (C₁ - (n : ℝ) * C₂)) := by
    have := hC₁'.sub hC₂'
    refine this.congr (fun s => ?_)
    ring

  refine ⟨C₁ - (n : ℝ) * C₂, hMain.congr (fun s => ?_)⟩
  simp only [one_div, Real.log_inv]
  ring

theorem poleOrder_implies_dirichletDensity_limit
    {K : Type*} [Field K] [NumberField K]
    {S : Set (Prime' K)} {n : ℕ+} {m : ℤ}
    (hm : HasMeromorphicContinuationWithPoleOrder
             (partialDedekindZeta K S ^ (n : ℕ)) m) :
    Filter.Tendsto (fun s : ℝ =>
      (∑' (𝔭 : S), ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) /
      Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((m : ℝ) / (n : ℝ))) := by

  obtain ⟨C, hC⟩ := eulerProduct_log_asymptotic hm

  set D : ℝ → ℝ := fun s =>
    ∑' (𝔭 : S), ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))
  set L : ℝ → ℝ := fun s => Real.log (1 / (s - 1))

  have hL : Filter.Tendsto L (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop := by
    have h_sub : Filter.Tendsto (fun s : ℝ => s - 1)
        (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 0 (Set.Ioi 0)) := by
      apply Filter.Tendsto.inf
      · have : Filter.Tendsto (fun s : ℝ => s - 1) (nhds 1) (nhds (1 - 1)) :=
          (continuous_id.sub continuous_const).continuousAt
        simpa using this
      · rw [Filter.tendsto_principal_principal]
        intro s hs; simp only [Set.mem_Ioi] at hs ⊢; linarith
    have h_neg_log : Filter.Tendsto (fun s : ℝ => -Real.log (s - 1))
        (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop :=
      Filter.tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h_sub)
    exact h_neg_log.congr' (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi] at hs
      show -Real.log (s - 1) = L s
      simp only [L, one_div, Real.log_inv])

  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast n.pos

  have h_ratio_zero : Filter.Tendsto
      (fun s => (↑n * D s - ↑m * L s) / (↑n * L s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
    hC.div_atTop (hL.const_mul_atTop hn)

  have h_eq : (fun s => (m : ℝ) / (n : ℝ) + (↑n * D s - ↑m * L s) / (↑n * L s))
      =ᶠ[nhdsWithin 1 (Set.Ioi 1)] (fun s => D s / L s) := by
    filter_upwards [hL.eventually (Filter.eventually_ge_atTop 1)] with s hgs
    have hgs' : L s ≠ 0 := by linarith
    have hn' : (n : ℝ) ≠ 0 := ne_of_gt hn
    field_simp
    ring

  rw [show ((m : ℝ) / (n : ℝ)) = (m : ℝ) / (n : ℝ) + 0 from by ring]
  exact (Filter.Tendsto.add tendsto_const_nhds h_ratio_zero).congr' h_eq

theorem partialDedekindZeta_poleOrder_nonneg {K : Type*} [Field K] [NumberField K]
    {S : Set (Prime' K)} {n : ℕ+} {m : ℤ}
    (h : HasMeromorphicContinuationWithPoleOrder (partialDedekindZeta K S ^ (n : ℕ)) m) :
    0 ≤ m := by


  have hlim := poleOrder_implies_dirichletDensity_limit h


  have h_nonneg : (0 : ℝ) ≤ (m : ℝ) / (n : ℝ) := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (1:ℝ) < 2 by norm_num))] with s hs1 hs2
    have h1 : 1 < s := hs1
    have h2 : s < 2 := hs2
    apply div_nonneg
    · exact tsum_nonneg fun 𝔭 => Real.rpow_nonneg (Nat.cast_nonneg _) _
    · apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith : (0:ℝ) < s - 1)]
      linarith

  have hn : (0 : ℝ) < (n : ℝ) := by positivity
  rw [le_div_iff₀ hn, zero_mul] at h_nonneg
  exact_mod_cast h_nonneg

theorem polar_implies_dirichlet {K : Type*} [Field K] [NumberField K]
    {S : Set (Prime' K)} {ρ : ℚ} (h : HasPolarDensity K S ρ) :
    HasDirichletDensity K S ρ := by
  obtain ⟨n, m, hm, hρ⟩ := h

  have hlim := poleOrder_implies_dirichletDensity_limit hm

  have hcast : (ρ : ℝ) = (m : ℝ) / (n : ℝ) := by rw [hρ]; push_cast; ring
  unfold HasDirichletDensity
  rwa [hcast]

theorem hasPolarDensity_nonneg {K : Type*} [Field K] [NumberField K]
    {S : Set (Prime' K)} {ρ : ℚ} (h : HasPolarDensity K S ρ) : 0 ≤ ρ := by
  obtain ⟨n, m, hm, hρ⟩ := h
  rw [hρ]
  apply div_nonneg
  · exact_mod_cast partialDedekindZeta_poleOrder_nonneg hm
  · exact_mod_cast n.pos.le


noncomputable def PolarDensity (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) : Option ℚ :=
  open Classical in
  if h : ∃ ρ : ℚ, HasPolarDensity K S ρ then some h.choose else none

noncomputable def DirichletDensity (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) : Option ℚ :=
  open Classical in
  if h : ∃ ρ : ℚ, HasDirichletDensity K S ρ then some h.choose else none

noncomputable def NaturalDensity (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) : Option ℚ :=
  open Classical in
  if h : ∃ ρ : ℚ, HasNaturalDensity K S ρ then some h.choose else none


lemma dirichletDensity_eq_some_iff {S : Set (Prime' K)} {ρ : ℚ} :
    DirichletDensity K S = some ρ ↔ HasDirichletDensity K S ρ := by
  classical
  constructor
  · intro h
    unfold DirichletDensity at h
    split_ifs at h with hex
    exact (Option.some_injective _ h) ▸ hex.choose_spec
  · intro h
    unfold DirichletDensity
    rw [dif_pos ⟨ρ, h⟩]
    congr 1
    exact hasDirichletDensity_unique (Exists.choose_spec ⟨ρ, h⟩) h

lemma naturalDensity_eq_some_iff {S : Set (Prime' K)} {ρ : ℚ} :
    NaturalDensity K S = some ρ ↔ HasNaturalDensity K S ρ := by
  classical
  constructor
  · intro h
    unfold NaturalDensity at h
    split_ifs at h with hex
    exact (Option.some_injective _ h) ▸ hex.choose_spec
  · intro h
    unfold NaturalDensity
    rw [dif_pos ⟨ρ, h⟩]
    congr 1
    exact hasNaturalDensity_unique (Exists.choose_spec ⟨ρ, h⟩) h





def IsDegreeOne (𝔭 : Prime' K) : Prop :=
  Nat.Prime (Ideal.absNorm 𝔭.asIdeal)







theorem partialDedekindZeta_dirichletSeries_summable
    {K : Type*} [Field K] [NumberField K]
    (S : Set (Prime' K)) (s : ℝ) (hs : 1 < s) :
    Summable (fun (𝔭 : S) => ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) :=
  (summable_primeIdeal_absNorm_rpow' K s hs).subtype S


lemma HasMeromorphicContinuationWithPoleOrder_mul {f g : ℂ → ℂ} {m₁ m₂ : ℤ}
    (hf : HasMeromorphicContinuationWithPoleOrder f m₁)
    (hg : HasMeromorphicContinuationWithPoleOrder g m₂) :
    HasMeromorphicContinuationWithPoleOrder (f * g) (m₁ + m₂) := by
  refine ⟨hf.1.mul hg.1, ?_⟩
  rw [meromorphicOrderAt_mul hf.1 hg.1, hf.2, hg.2]
  simp only [← WithTop.coe_add, Int.neg_add]

lemma HasMeromorphicContinuationWithPoleOrder_pow {f : ℂ → ℂ} {m : ℤ} {n : ℕ}
    (hf : HasMeromorphicContinuationWithPoleOrder f m) :
    HasMeromorphicContinuationWithPoleOrder (f ^ n) (m * n) := by
  refine ⟨hf.1.pow n, ?_⟩
  rw [meromorphicOrderAt_pow hf.1, hf.2]
  have : (↑n : WithTop ℤ) * ↑(-m) = ↑(↑n * (-m) : ℤ) := by exact_mod_cast rfl
  rw [this]; congr 1; ring



lemma partialDedekindZeta_finite_meromorphicOrderAt_zero
    {K : Type*} [Field K] [NumberField K]
    (S : Set (Prime' K)) (hS : S.Finite) :
    meromorphicOrderAt (partialDedekindZeta K S) 1 = 0 := by
  haveI : Fintype ↥S := hS.fintype
  let F : ↥S → ℂ → ℂ := fun 𝔭 s =>
    (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s))⁻¹
  have heq : partialDedekindZeta K S = fun s => ∏ 𝔭 : ↥S, F 𝔭 s := by
    ext s; exact tprod_fintype _
  rw [heq]
  have hne_cast : ∀ (𝔭 : ↥S), (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ≠ 0 := by
    intro 𝔭
    have : Ideal.absNorm (𝔭 : Prime' K).asIdeal ≠ 0 := by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm (𝔭 : Prime' K)
      omega
    exact Nat.cast_ne_zero.mpr this
  have hfactor_analytic : ∀ (𝔭 : ↥S), AnalyticAt ℂ (F 𝔭) 1 := by
    intro 𝔭
    have hne := hne_cast 𝔭
    show AnalyticAt ℂ (fun s => (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s))⁻¹) 1
    apply AnalyticAt.inv
    · apply AnalyticAt.sub analyticAt_const
      have hrw : ∀ s : ℂ, (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s) =
          Complex.exp (-s * Complex.log (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ)) := by
        intro s; rw [Complex.cpow_def_of_ne_zero hne]; ring_nf
      simp_rw [hrw]
      exact ((analyticAt_id (𝕜 := ℂ)).neg.mul analyticAt_const).cexp
    · have hN_gt : 1 < Ideal.absNorm (𝔭 : Prime' K).asIdeal :=
        NumberField.HeightOneSpectrum.one_lt_absNorm (𝔭 : Prime' K)
      rw [show (-(1 : ℂ)) = (-1 : ℤ) by push_cast; ring, Complex.cpow_intCast]
      simp only [zpow_neg_one]
      rw [sub_ne_zero]
      intro h
      have h2 : (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) = 1 := by
        rw [eq_comm, inv_eq_one] at h; exact h
      have : Ideal.absNorm (𝔭 : Prime' K).asIdeal = 1 := by exact_mod_cast h2
      omega
  have hprod_analytic : AnalyticAt ℂ (fun s => ∏ 𝔭 : ↥S, F 𝔭 s) 1 :=
    Finset.analyticAt_fun_prod Finset.univ (fun 𝔭 _ => hfactor_analytic 𝔭)
  have hprod_ne : (fun s => ∏ 𝔭 : ↥S, F 𝔭 s) (1 : ℂ) ≠ 0 := by
    simp only
    apply Finset.prod_ne_zero_iff.mpr
    intro 𝔭 _
    simp only [F]
    apply inv_ne_zero
    have hN_gt : 1 < Ideal.absNorm (𝔭 : Prime' K).asIdeal :=
      NumberField.HeightOneSpectrum.one_lt_absNorm (𝔭 : Prime' K)
    rw [show (-(1 : ℂ)) = (-1 : ℤ) by push_cast; ring, Complex.cpow_intCast]
    simp only [zpow_neg_one]
    rw [sub_ne_zero]
    intro h
    have h2 : (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) = 1 := by
      rw [eq_comm, inv_eq_one] at h; exact h
    have : Ideal.absNorm (𝔭 : Prime' K).asIdeal = 1 := by exact_mod_cast h2
    omega
  rw [hprod_analytic.meromorphicOrderAt_eq,
      hprod_analytic.analyticOrderAt_eq_zero.mpr hprod_ne]
  simp




















def SplitsCompletely (K L : Type u) [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Prime' K) : Prop :=
  FrobeniusAutomorphism K L 𝔭 = 1

def Spl (K L : Type u) [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [IsGalois K L] : Set (Prime' K) :=
  {𝔭 | SplitsCompletely K L 𝔭}

def SplitsCompletelyGen (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
    𝔔.asIdeal.LiesOver 𝔭.asIdeal →
    𝔭.asIdeal.ramificationIdx 𝔔.asIdeal = 1 ∧ 𝔭.asIdeal.inertiaDeg 𝔔.asIdeal = 1

def SplGen (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] : Set (Prime' K) :=
  {𝔭 | SplitsCompletelyGen K L 𝔭}














def FinSymmDiff (S T : Set (Prime' K)) : Prop :=
  Set.Finite (symmDiff S T)

def PrimeSetLe (S T : Set (Prime' K)) : Prop :=
  Set.Finite (S \ T)



lemma adjoin_range_eq_fieldRange {K' L' E' : Type*} [Field K'] [Field L'] [Field E']
    [Algebra K' L'] [Algebra K' E'] (f : L' →ₐ[K'] E') :
    IntermediateField.adjoin K' (Set.range f) = f.fieldRange :=
  le_antisymm (IntermediateField.adjoin_le_iff.mpr fun _ ⟨y, hy⟩ => ⟨y, hy⟩)
    (fun _ ⟨y, hy⟩ => IntermediateField.subset_adjoin K' _ ⟨y, hy⟩)

lemma inclusion_fieldRange_sup_eq_top {K' A' : Type*} [Field K'] [Field A'] [Algebra K' A']
    {E' F' : IntermediateField K' A'} :
    (IntermediateField.inclusion (le_sup_left : E' ≤ E' ⊔ F')).fieldRange ⊔
    (IntermediateField.inclusion (le_sup_right : F' ≤ E' ⊔ F')).fieldRange = ⊤ :=
  IntermediateField.map_injective (E' ⊔ F').val (by
    rw [IntermediateField.map_sup, AlgHom.map_fieldRange, AlgHom.map_fieldRange,
      show (E' ⊔ F').val.comp (IntermediateField.inclusion le_sup_left) = E'.val from by ext; rfl,
      show (E' ⊔ F').val.comp (IntermediateField.inclusion le_sup_right) = F'.val from by ext; rfl,
      IntermediateField.fieldRange_val, IntermediateField.fieldRange_val,
      ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val])

lemma comp_equiv_fieldRange {K' L' E' F' : Type*}
    [Field K'] [Field L'] [Field E'] [Field F']
    [Algebra K' L'] [Algebra K' E'] [Algebra K' F']
    (f : E' →ₐ[K'] F') (g : L' ≃ₐ[K'] E') :
    (f.comp g.toAlgHom).fieldRange = f.fieldRange := by
  ext x; simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
  exact ⟨fun ⟨y, h⟩ => ⟨g y, h⟩, fun ⟨y, h⟩ => ⟨g.symm y, by simp [h]⟩⟩



















theorem split_iff_in_kernel (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [KroneckerWeber.IsAbelianExtension K L]
    (𝔪 : Modulus K) (𝔭 : Prime' K)
    (h_coprime : 𝔪 (Place.finite 𝔭) = 0) :
    SplitsCompletely K L 𝔭 ↔ ArtinMap K L 𝔪 (primeCoprime K 𝔪 𝔭 h_coprime) = 1 := by
  unfold SplitsCompletely
  rw [artinMap_at_prime_eq_frobenius]

lemma modulus_support_finite (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    Set.Finite {𝔭 : Prime' K | 𝔪 (Place.finite 𝔭) ≠ 0} := by
  have : {𝔭 : Prime' K | 𝔪 (Place.finite 𝔭) ≠ 0} =
    Place.finite ⁻¹' {v | 𝔪 v ≠ 0} := by ext; simp
  rw [this]
  exact 𝔪.finite_support.preimage (fun a _ b _ hab => by cases hab; rfl)





structure CongruenceSubgroupPair (K : Type u) [Field K] [NumberField K] where
  modulus : Modulus K
  subgroup : Subgroup (FracIdealsCoprime K modulus)
  ray_le : RayGroup K modulus ≤ subgroup

def CongruenceSubgroupPair.toAmbientSubgroup {K : Type u} [Field K] [NumberField K]
    (p : CongruenceSubgroupPair K) : Subgroup (FracIdeal K)ˣ :=
  p.subgroup.map (FracIdealsCoprime_subgroup K p.modulus).subtype

def CongruenceSubgroupPair.IsEquiv {K : Type u} [Field K] [NumberField K]
    (p₁ p₂ : CongruenceSubgroupPair K) : Prop :=
  (FracIdealsCoprime_subgroup K p₁.modulus) ⊓ p₂.toAmbientSubgroup =
  (FracIdealsCoprime_subgroup K p₂.modulus) ⊓ p₁.toAmbientSubgroup


def IsHilbertClassField (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [KroneckerWeber.IsAbelianExtension K L] : Prop :=
  IsRayClassField K L Modulus.trivial


end RayClassField
