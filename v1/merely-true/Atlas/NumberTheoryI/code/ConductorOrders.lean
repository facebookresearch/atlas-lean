/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Conductor
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.Algebra.Module.Lattice
import Mathlib.Tactic.LinearCombination

noncomputable section

open Ideal Polynomial Algebra IsDedekindDomain nonZeroDivisors

section ConductorDef

variable (R : Type*) (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

def Subalgebra.conductorIdeal (A : Subalgebra R S) : Ideal S where
  carrier := {a : S | ∀ b : S, a * b ∈ A}
  zero_mem' b := by simp [A.zero_mem]
  add_mem' {a₁ a₂} ha₁ ha₂ b := by rw [add_mul]; exact A.add_mem (ha₁ b) (ha₂ b)
  smul_mem' c a ha b := by
    simp only [smul_eq_mul, Set.mem_setOf_eq] at *
    rw [show c * a * b = a * (c * b) by ring]
    exact ha (c * b)

variable {R S}

end ConductorDef

section OrderDef

class IsOrder (O : Type*) [CommRing O] [IsDomain O] : Prop where
  isNoetherian : IsNoetherianRing O
  dimLEOne : Ring.DimensionLEOne O
  notIsField : ¬ IsField O
  intClosureFG : ∀ (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K],
    Module.Finite O (integralClosure O K)

class IsAOrder (A : Type*) (L : Type*) [CommRing A] [CommRing L] [Algebra A L]
    (O : Subalgebra A L) : Prop where
  fg : (O.toSubmodule).FG
  spans : ∀ (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [IsScalarTower A K L],
    Submodule.span K (Set.range (Subtype.val : O → L)) = ⊤

end OrderDef

section ConductorFiniteness

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem conductor_ne_bot_of_fg_subalgebra
    {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Subalgebra R K) (hS : S.toSubmodule.FG) :
    ∃ (d : R), d ≠ 0 ∧ ∀ s ∈ S, algebraMap R K d * s ∈ (algebraMap R K).range := by
  obtain ⟨t, ht⟩ := hS
  obtain ⟨⟨d, hd_mem⟩, hd⟩ := IsLocalization.exist_integer_multiples_of_finset R⁰ t
  refine ⟨d, nonZeroDivisors.ne_zero hd_mem, ?_⟩
  suffices h : ∀ s ∈ Submodule.span R (t : Set K),
      algebraMap R K d * s ∈ (algebraMap R K).range by
    intro s hs; exact h s (by rwa [ht])
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    have hint := hd x hx
    unfold IsLocalization.IsInteger at hint
    simp only [Algebra.smul_def] at hint
    exact hint
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]; exact Subring.add_mem _ hx hy
  | smul r x _ hx =>
    rw [Algebra.smul_def, ← mul_assoc, mul_comm (algebraMap R K d), mul_assoc]
    exact Subring.mul_mem _ ⟨r, rfl⟩ hx

theorem conductor_ne_bot_iff_module_finite
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Subalgebra R K) :
    (∃ (d : R), d ≠ 0 ∧ ∀ s ∈ S, algebraMap R K d * s ∈ (algebraMap R K).range) ↔
      S.toSubmodule.FG := by
  constructor
  ·
    rintro ⟨d, hd, hd_mem⟩
    have hinj := IsFractionRing.injective R K
    have hd' : algebraMap R K d ≠ 0 := by
      intro h; exact hd (hinj (by rw [h, map_zero]))
    let mulD : K →ₗ[R] K := DistribSMul.toLinearMap R K (algebraMap R K d)
    have hmulD_inj : Function.Injective mulD := by
      intro a b h
      change algebraMap R K d * a = algebraMap R K d * b at h
      exact mul_left_cancel₀ hd' h
    have himage : Submodule.map mulD S.toSubmodule ≤ (⊥ : Subalgebra R K).toSubmodule := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := hx
      change algebraMap R K d * s ∈ (⊥ : Subalgebra R K)
      exact Algebra.mem_bot.mpr (hd_mem s hs)
    have hbot_fg : (⊥ : Subalgebra R K).toSubmodule.FG := by
      have : (⊥ : Subalgebra R K).toSubmodule = LinearMap.range (Algebra.linearMap R K) := by
        ext x; simp [Algebra.mem_bot, Algebra.linearMap_apply]
      rw [this, LinearMap.range_eq_map]
      exact (IsNoetherian.noetherian (⊤ : Submodule R R)).map _
    exact Submodule.fg_of_fg_map_injective mulD hmulD_inj (hbot_fg.of_le himage)
  ·
    exact conductor_ne_bot_of_fg_subalgebra S

end ConductorFiniteness

section OrderFiniteGeneration

end OrderFiniteGeneration

section FinitePrimeDivisors

theorem finite_primes_containing_ideal {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    {𝔠 : Ideal B} (h𝔠 : 𝔠 ≠ ⊥) :
    Set.Finite {𝔭 : Ideal B | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ 𝔠 ≤ 𝔭} := by
  have hfin : Set.Finite {v : HeightOneSpectrum B | v.asIdeal ∣ 𝔠} :=
    Ideal.finite_factors h𝔠
  apply Set.Finite.subset (hfin.image (fun v => v.asIdeal))
  intro 𝔭 ⟨h𝔭_prime, h𝔭_ne, h𝔭_le⟩
  simp only [Set.mem_image, Set.mem_setOf_eq]
  haveI := h𝔭_prime
  have h𝔭_div : 𝔭 ∣ 𝔠 := Ideal.dvd_iff_le.mpr h𝔭_le
  haveI : 𝔭.IsMaximal := h𝔭_prime.isMaximal h𝔭_ne
  exact ⟨⟨𝔭, h𝔭_prime, h𝔭_ne⟩, h𝔭_div, rfl⟩

end FinitePrimeDivisors

section LocalizationBijectionCoprime

end LocalizationBijectionCoprime

section PrimeConductorEquivalences

end PrimeConductorEquivalences

section CoprimePrimeFactorization

end CoprimePrimeFactorization

section CoprimePrimeResidueField

end CoprimePrimeResidueField

section CoprimeDegreeFormula

open UniqueFactorizationMonoid in

open UniqueFactorizationMonoid in

open UniqueFactorizationMonoid in
theorem order_prime_decomposition
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {x : S} {I : Ideal R}
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDedekindDomain S]
    [Module.IsTorsionFree R S]
    (hI : I.IsMaximal) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) :
    let e := KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx'
    ∀ {J : Ideal S} (hJ : J ∈ normalizedFactors (I.map (algebraMap R S))),
      emultiplicity J (I.map (algebraMap R S)) =
        emultiplicity (↑(e ⟨J, hJ⟩))
          (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) :=
  fun hJ => KummerDedekind.emultiplicity_factors_map_eq_emultiplicity hI hI' hx hx' hJ

end CoprimeDegreeFormula

end

section FractionalIdealPrimeTo

open nonZeroDivisors

variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
lemma nonZeroDivisors_le_comap_atPrime (𝔭 : Ideal A) [𝔭.IsPrime] :
    A⁰ ≤ Submonoid.comap (algebraMap A (Localization.AtPrime 𝔭)) (Localization.AtPrime 𝔭)⁰ := by
  intro a ha
  rw [Submonoid.mem_comap]
  exact IsLocalization.map_nonZeroDivisors_le 𝔭.primeCompl (Localization.AtPrime 𝔭) ⟨a, ha, rfl⟩


def FractionalIdeal.IsPrimeTo [IsNoetherianRing A]
    (I : FractionalIdeal A⁰ (Localization A⁰)) (J : Ideal A) : Prop :=
  ∀ (𝔭 : Ideal A) [𝔭.IsPrime], J ≤ 𝔭 →
    FractionalIdeal.extended (Localization A⁰) (nonZeroDivisors_le_comap_atPrime 𝔭) I = 1

variable [IsNoetherianRing A]

def invertibleFractionalIdealsPrimeTo (J : Ideal A) :
    Subgroup (FractionalIdeal A⁰ (Localization A⁰))ˣ where
  carrier := {u | (u : FractionalIdeal A⁰ (Localization A⁰)).IsPrimeTo J}
  one_mem' := by
    intro 𝔭 _ _
    exact FractionalIdeal.extended_one _ _
  mul_mem' := by
    intro a b ha hb 𝔭 _ h𝔭
    simp only [Units.val_mul]
    rw [FractionalIdeal.extended_mul, ha 𝔭 h𝔭, hb 𝔭 h𝔭, one_mul]
  inv_mem' := by
    intro a ha 𝔭 _ h𝔭
    have h1 : FractionalIdeal.extended (Localization A⁰) (nonZeroDivisors_le_comap_atPrime 𝔭)
        (↑(a * a⁻¹) : FractionalIdeal A⁰ (Localization A⁰)) = 1 := by
      simp [FractionalIdeal.extended_one]
    rw [Units.val_mul, FractionalIdeal.extended_mul, ha 𝔭 h𝔭, one_mul] at h1
    exact h1

end FractionalIdealPrimeTo

section FaithfulStatements

class IsAOrder_AKLB (A : Type*) (L : Type*)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing L] [IsDomain L] [Algebra A L]
    (O : Subalgebra A L) : Prop where
  fg : (O.toSubmodule).FG
  spans : ∀ (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [IsScalarTower A K L],
    Submodule.span K (Set.range (Subtype.val : O → L)) = ⊤

theorem order_iff_fg_integral
    {A : Type*} {K : Type*} {L : Type*} {B : Type*}
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra A B]
    [CommRing L] [IsDomain L] [Algebra A L] [Algebra K L] [Algebra B L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [Module.Finite A B]
    (O : Subalgebra A L)
    [IsFractionRing (↥O) L]
    (hA : ¬ IsField A) :
    IsAOrder_AKLB A L O ↔
      (IsOrder O ∧ IsIntegralClosure B (↥O) L) := by
  constructor
  ·
    intro h
    haveI : Module.Finite A ↥O := Module.Finite.iff_fg.mpr h.fg
    haveI : Algebra.IsIntegral A ↥O := Algebra.IsIntegral.of_finite A ↥O
    constructor
    ·
      exact {
        isNoetherian := IsNoetherianRing.of_finite A ↥O
        dimLEOne := by
          haveI : IsIntegralClosure ↥O A ↥O := {
            algebraMap_injective := fun _ _ h => h
            isIntegral_iff := by
              intro x
              exact ⟨fun _ => ⟨x, rfl⟩,
                fun ⟨y, hy⟩ => hy ▸ Algebra.IsIntegral.isIntegral y⟩
          }
          exact Ring.DimensionLEOne.isIntegralClosure A ↥O ↥O
        notIsField := by
          intro hOfield
          have hinj : Function.Injective (algebraMap A ↥O) := by
            have h_AL : Function.Injective (algebraMap A L) := by
              rw [IsScalarTower.algebraMap_eq A K L]
              exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
            intro x y hxy
            apply h_AL
            have : algebraMap ↥O L (algebraMap A ↥O x) =
                algebraMap ↥O L (algebraMap A ↥O y) := congr_arg _ hxy
            simp only [← IsScalarTower.algebraMap_apply] at this
            exact this
          exact hA (isField_of_isIntegral_of_isField hinj hOfield)
        intClosureFG := by
          intro K' _ _ _


          have hunits : ∀ (s : ↥(nonZeroDivisors ↥O)),
              IsUnit (algebraMap ↥O L (s : ↥O)) := by
            intro ⟨s, hs⟩
            have hne : algebraMap ↥O L s ≠ 0 := by
              intro h0
              exact nonZeroDivisors.ne_zero hs
                (Subtype.val_injective (by change (s : L) = 0; exact h0))
            have hintA : IsIntegral A (algebraMap ↥O L s) := by
              rw [show algebraMap ↥O L s = (s : L) from rfl]
              exact (Algebra.IsIntegral.isIntegral (R := A) s).map (O.val)
            exact (hintA.tower_top (R := A) (A := K)).isUnit hne

          let f : K' →+* L := IsLocalization.lift (M := nonZeroDivisors ↥O) hunits

          letI algOB : Algebra ↥O B :=
            (IsIntegralClosure.lift A B L : ↥O →ₐ[A] B).toRingHom.toAlgebra
          haveI : IsScalarTower A ↥O B :=
            IsScalarTower.of_algebraMap_eq
              (fun a => ((IsIntegralClosure.lift A B L : ↥O →ₐ[A] B).commutes a).symm)

          haveI : Module.Finite ↥O B :=
            Module.Finite.of_restrictScalars_finite A ↥O B
          haveI : IsNoetherianRing ↥O := IsNoetherianRing.of_finite A ↥O
          haveI : IsNoetherian ↥O B :=
            isNoetherian_of_isNoetherianRing_of_finite ↥O B

          haveI hIC_BO : IsIntegralClosure B ↥O L := {
            algebraMap_injective := IsIntegralClosure.algebraMap_injective B A L
            isIntegral_iff := by
              intro x
              constructor
              · intro hx
                exact (IsIntegralClosure.isIntegral_iff (A := B) (R := A)).mp
                  (isIntegral_trans x hx)
              · intro ⟨b, hb⟩
                have hAx : IsIntegral A x := by
                  rw [← hb]
                  exact (IsIntegralClosure.isIntegral_iff (A := B) (R := A)).mpr ⟨b, rfl⟩
                exact hAx.tower_top
          }

          haveI : IsScalarTower ↥O B L :=
            IsScalarTower.of_algebraMap_eq (fun x => by
              change algebraMap ↥O L x = algebraMap B L ((IsIntegralClosure.lift A B L : ↥O →ₐ[A] B) x)
              rw [IsIntegralClosure.algebraMap_lift])


          have hf_comp : (algebraMap ↥O L).comp (RingHom.id ↥O) =
              f.comp (algebraMap ↥O K') := by
            ext y
            simp only [RingHom.comp_apply, RingHom.id_apply]
            exact (IsLocalization.lift_eq hunits y).symm


          have hg_int : ∀ (x : ↥(integralClosure ↥O K')),
              IsIntegral ↥O (f (x : K')) :=
            fun x => IsIntegral.map_of_comp_eq (RingHom.id ↥O) f hf_comp x.2
          let g : ↥(integralClosure ↥O K') → B :=
            fun x => IsIntegralClosure.mk' (R := ↥O) B (f (x : K')) (hg_int x)

          have hg_inj : Function.Injective g := by
            intro x y hxy
            have h1 : algebraMap B L (g x) = algebraMap B L (g y) := congrArg _ hxy
            rw [IsIntegralClosure.algebraMap_mk' (R := ↥O),
                IsIntegralClosure.algebraMap_mk' (R := ↥O)] at h1
            exact Subtype.val_injective (RingHom.injective f h1)

          have hg_add : ∀ x y, g (x + y) = g x + g y := by
            intro x y
            apply IsIntegralClosure.algebraMap_injective B ↥O L
            rw [IsIntegralClosure.algebraMap_mk' (R := ↥O), map_add,
                IsIntegralClosure.algebraMap_mk' (R := ↥O),
                IsIntegralClosure.algebraMap_mk' (R := ↥O)]
            exact map_add f _ _

          have hg_smul : ∀ (o : ↥O) (x : ↥(integralClosure ↥O K')),
              g (o • x) = o • g x := by
            intro o x
            apply IsIntegralClosure.algebraMap_injective B ↥O L
            rw [IsIntegralClosure.algebraMap_mk' (R := ↥O),
                Algebra.smul_def (r := o) (x := g x), map_mul,
                ← IsScalarTower.algebraMap_apply ↥O B L,
                IsIntegralClosure.algebraMap_mk' (R := ↥O)]
            show f (↑(o • x) : K') = algebraMap ↥O L o * f (↑x : K')
            rw [show (↑(o • x) : K') = algebraMap ↥O K' o * (↑x : K') from
                  Algebra.smul_def o (↑x : K'),
                map_mul, IsLocalization.lift_eq hunits]

          let glin : ↥(integralClosure ↥O K') →ₗ[↥O] B := {
            toFun := g
            map_add' := hg_add
            map_smul' := fun o x => by
              simp only [RingHom.id_apply]
              exact hg_smul o x
          }

          haveI : IsNoetherian ↥O ↥(integralClosure ↥O K') :=
            isNoetherian_of_ker_bot glin (LinearMap.ker_eq_bot.mpr hg_inj)
          exact inferInstance
      }
    ·
      exact {
        algebraMap_injective := IsIntegralClosure.algebraMap_injective B A L
        isIntegral_iff := by
          intro x
          constructor
          · intro hx
            have hAx : IsIntegral A x := isIntegral_trans x hx
            exact (IsIntegralClosure.isIntegral_iff (A := B) (R := A)).mp hAx
          · intro ⟨b, hb⟩
            have hAx : IsIntegral A x := by
              rw [← hb]
              exact (IsIntegralClosure.isIntegral_iff (A := B) (R := A)).mpr ⟨b, rfl⟩
            exact hAx.tower_top
      }
  ·
    intro ⟨hOrd, hIC⟩

    have hfg_O : (O.toSubmodule).FG := by

      have hFG : (LinearMap.range (IsScalarTower.toAlgHom A B L).toLinearMap).FG := by
        rw [LinearMap.range_eq_map]
        exact Submodule.FG.map _ ((Module.Finite.iff_fg).mp inferInstance)

      have hle : O.toSubmodule ≤
          LinearMap.range (IsScalarTower.toAlgHom A B L).toLinearMap := by
        intro x hx
        rw [LinearMap.mem_range]
        have hxO : IsIntegral (↥O) x := by
          have : x = algebraMap (↥O) L ⟨x, hx⟩ := by simp
          rw [this]
          exact isIntegral_algebraMap
        obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B) (R := ↥O)).mp hxO
        exact ⟨b, hb⟩

      exact hFG.of_le hle
    exact {
      fg := hfg_O
      spans := by
        intro K' _ _ _ _ _
        haveI : Module.Finite A ↥O := Module.Finite.iff_fg.mpr hfg_O
        haveI : Algebra.IsIntegral A ↥O := Algebra.IsIntegral.of_finite A ↥O
        haveI : NoZeroDivisors ↥O := O.noZeroDivisors
        haveI : FaithfulSMul A ↥O := by
          constructor
          intro r s h
          have hinj : Function.Injective (algebraMap A L) := by
            rw [IsScalarTower.algebraMap_eq A K' L]
            exact (algebraMap K' L).injective.comp (IsFractionRing.injective A K')
          apply hinj
          have h1 := h (1 : ↥O)
          simp only [Algebra.smul_def, mul_one] at h1
          have := congr_arg (algebraMap ↥O L) h1
          simp only [← IsScalarTower.algebraMap_apply] at this
          exact this
        haveI : Algebra.IsAlgebraic A ↥O := Algebra.IsIntegral.isAlgebraic
        have hrank : Module.rank K' L = Module.rank A ↥O :=
          Algebra.IsAlgebraic.rank_of_isFractionRing A K' ↥O L
        haveI : Module.Finite K' L := by
          have h1 : Module.rank A ↥O < Cardinal.aleph0 := Module.rank_lt_aleph0 A ↥O
          have h2 : Module.rank K' L < Cardinal.aleph0 := hrank ▸ h1
          exact Module.rank_lt_aleph0_iff.mp h2
        have hle : Module.rank K' L ≤ Module.rank A ↥O := hrank.le
        have hspa := Submodule.span_range_eq_top_of_injective_of_rank_le
          (R := A) (K := K') (f := O.val.toLinearMap)
          (Subtype.val_injective) hle
        convert hspa using 1
    }

lemma conductor_span_helper
    {O B : Type*} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B]
    [Algebra O B]
    {𝔠 𝔭 : Ideal O}
    (h𝔠_cond : ∀ c ∈ 𝔠, ∀ b : B, algebraMap O B c * b ∈ (algebraMap O B).range)
    {s : O} (hs𝔠 : s ∈ 𝔠)
    {x : B} (hx : x ∈ 𝔭.map (algebraMap O B)) :
    ∃ n : ℕ, ∃ q ∈ 𝔭, algebraMap O B q = (algebraMap O B s) ^ n * x := by
  set f := algebraMap O B; set fs := f s
  change x ∈ Ideal.span (f '' ↑𝔭) at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨p, hp, rfl⟩ := hy; exact ⟨0, p, hp, by simp⟩
  | zero => exact ⟨0, 0, 𝔭.zero_mem, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨nx, qx, hqx, hfqx⟩ := ihx; obtain ⟨ny, qy, hqy, hfqy⟩ := ihy
    refine ⟨max nx ny, s ^ (max nx ny - nx) * qx + s ^ (max nx ny - ny) * qy,
      𝔭.add_mem (𝔭.mul_mem_left _ hqx) (𝔭.mul_mem_left _ hqy), ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, hfqx, hfqy, mul_add]; congr 1
    · rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_max_left nx ny)]
    · rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_max_right nx ny)]
  | smul b x _ ihx =>
    obtain ⟨n, q, hq, hfq⟩ := ihx; obtain ⟨r, hr⟩ := h𝔠_cond s hs𝔠 b
    refine ⟨n + 1, r * q, 𝔭.mul_mem_left r hq, ?_⟩
    simp only [map_mul, pow_succ, smul_eq_mul]; rw [hfq, hr]; ring

theorem ideal_extension_prime_coprime_conductor
    {O : Type*} {B : Type*}
    [CommRing O] [IsDomain O]
    [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra O B]
    (hf : Function.Injective (algebraMap O B))
    {𝔠 : Ideal O} {𝔭 : Ideal O} [h𝔭 : 𝔭.IsPrime]

    (h𝔠_cond : ∀ c ∈ 𝔠, ∀ b : B, algebraMap O B c * b ∈ (algebraMap O B).range)


    (h_sup : 𝔠 ⊔ 𝔭 = ⊤)
    (h𝔭_not_contain : ¬ 𝔠 ≤ 𝔭) :
    (𝔭.map (algebraMap O B)).IsPrime := by
  set f := algebraMap O B; set 𝔭B := 𝔭.map f
  set φ := Ideal.quotientMap 𝔭B f Ideal.le_comap_map

  have h_inj : Function.Injective φ := by
    apply Ideal.quotientMap_injective'
    intro a ha; change f a ∈ 𝔭B at ha
    obtain ⟨s, hs𝔠, hs𝔭⟩ := Set.not_subset.mp h𝔭_not_contain
    obtain ⟨n, q, hq, hfq⟩ := conductor_span_helper h𝔠_cond hs𝔠 ha
    have h_eq : q = s ^ n * a := hf (by rw [map_mul, map_pow, hfq])
    rw [h_eq] at hq
    exact (h𝔭.mem_or_mem hq).resolve_left (mt (Ideal.IsPrime.mem_of_pow_mem h𝔭 n) hs𝔭)

  have h_surj : Function.Surjective φ := by
    have h1 : (1 : O) ∈ 𝔠 ⊔ 𝔭 := h_sup ▸ Submodule.mem_top
    obtain ⟨c, hc, p, hp, hcp⟩ := Submodule.mem_sup.mp h1
    intro bbar; obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bbar
    obtain ⟨a, ha⟩ := h𝔠_cond c hc b
    refine ⟨Ideal.Quotient.mk 𝔭 a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    have hfc_fp : f c + f p = 1 := by rw [← map_add, hcp, map_one]
    have hsub : f a - b = -(f p * b) := by
      rw [ha]; have : f c = 1 - f p := by linear_combination hfc_fp
      rw [this]; ring
    rw [hsub]; apply 𝔭B.neg_mem
    rw [show f p * b = b * f p from mul_comm _ _]
    exact Ideal.mul_mem_left 𝔭B b (Ideal.mem_map_of_mem f hp)

  rw [← Ideal.Quotient.isDomain_iff_prime]
  haveI : IsDomain (O ⧸ 𝔭) := (Ideal.Quotient.isDomain_iff_prime 𝔭).mpr h𝔭
  haveI : Nontrivial (B ⧸ 𝔭B) := by
    constructor; use 0, 1; intro h01
    exact zero_ne_one (h_inj (by rw [map_zero, map_one]; exact h01))
  haveI : NoZeroDivisors (B ⧸ 𝔭B) := by
    constructor; intro a b hab
    obtain ⟨x, rfl⟩ := h_surj a; obtain ⟨y, rfl⟩ := h_surj b
    have hxy0 : x * y = 0 := h_inj (by rw [map_mul, hab, map_zero])
    rcases mul_eq_zero.mp hxy0 with hx | hy
    · left; rw [hx, map_zero]
    · right; rw [hy, map_zero]
  exact IsDomain.mk

theorem prime_bijection_coprime_conductor
    {O : Type*} {B : Type*}
    [CommRing O] [IsDomain O]
    [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra O B]
    (hf : Function.Injective (algebraMap O B))
    (𝔠 : Ideal O) (h𝔠_ne : 𝔠 ≠ ⊥)
    (h𝔠_cond : ∀ c ∈ 𝔠, ∀ b : B, algebraMap O B c * b ∈ (algebraMap O B).range)


    (h_sup : ∀ (𝔭 : Ideal O), 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ 𝔠 ≤ 𝔭 → 𝔠 ⊔ 𝔭 = ⊤) :
    ∃ (e : {𝔮 : Ideal B // 𝔮.IsPrime ∧ 𝔮 ≠ ⊥ ∧ ¬ (𝔠.map (algebraMap O B) ≤ 𝔮)} ≃
         {𝔭 : Ideal O // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ 𝔠 ≤ 𝔭}),

      (∀ 𝔮, (e 𝔮).1 = 𝔮.1.comap (algebraMap O B)) ∧

      (∀ 𝔭, (e.symm 𝔭).1 = 𝔭.1.map (algebraMap O B)) := by
  set f := algebraMap O B

  have comap_map_eq : ∀ (𝔭 : Ideal O), 𝔭.IsPrime → ¬ 𝔠 ≤ 𝔭 →
      Ideal.comap f (Ideal.map f 𝔭) = 𝔭 := by
    intro 𝔭 h𝔭_prime h𝔭_nc; apply le_antisymm
    · intro a ha
      obtain ⟨s, hs𝔠, hs𝔭⟩ := Set.not_subset.mp h𝔭_nc
      obtain ⟨n, q, hq, hfq⟩ := conductor_span_helper h𝔠_cond hs𝔠 (show f a ∈ _ from ha)
      have h_eq : q = s ^ n * a := hf (by rw [map_mul, map_pow, hfq])
      rw [h_eq] at hq
      exact (h𝔭_prime.mem_or_mem hq).resolve_left (mt (h𝔭_prime.mem_of_pow_mem n) hs𝔭)
    · exact Ideal.le_comap_map

  have comap_ne_bot : ∀ (𝔮 : Ideal B), 𝔮 ≠ ⊥ → Ideal.comap f 𝔮 ≠ ⊥ := by
    intro 𝔮 h𝔮_ne h_bot
    have ⟨c, hc𝔠, hc_ne⟩ : ∃ c ∈ 𝔠, c ≠ (0 : O) := by
      by_contra h; push Not at h
      exact h𝔠_ne (eq_bot_iff.mpr fun x hx => by simpa using h x hx)
    have ⟨b, hb𝔮, hb_ne⟩ : ∃ b ∈ 𝔮, b ≠ (0 : B) := by
      by_contra h; push Not at h
      exact h𝔮_ne (eq_bot_iff.mpr fun x hx => by simpa using h x hx)
    obtain ⟨a, ha⟩ := h𝔠_cond c hc𝔠 b
    have : a ∈ Ideal.comap f 𝔮 := by rw [Ideal.mem_comap, ha]; exact 𝔮.mul_mem_left _ hb𝔮
    rw [h_bot] at this; have := Ideal.mem_bot.mp this
    rw [this, map_zero] at ha
    exact hb_ne ((mul_eq_zero.mp ha.symm).resolve_left
      fun h => hc_ne (hf (by rw [h, map_zero])))


  have map_comap_eq : ∀ (𝔮 : Ideal B), 𝔮.IsPrime → 𝔮 ≠ ⊥ →
      ¬ Ideal.map f 𝔠 ≤ 𝔮 → Ideal.map f (Ideal.comap f 𝔮) = 𝔮 := by
    intro 𝔮 h𝔮p h𝔮ne h𝔮nc
    haveI : (Ideal.comap f 𝔮).IsPrime := Ideal.comap_isPrime f 𝔮
    have h𝔭_nc : ¬ 𝔠 ≤ Ideal.comap f 𝔮 := fun h => h𝔮nc (Ideal.map_le_of_le_comap h)
    have h𝔭_ne := comap_ne_bot 𝔮 h𝔮ne
    haveI : (Ideal.map f (Ideal.comap f 𝔮)).IsPrime :=
      ideal_extension_prime_coprime_conductor hf h𝔠_cond (h_sup _ inferInstance h𝔭_ne h𝔭_nc) h𝔭_nc
    haveI := h𝔮p
    exact (Ring.DimensionLeOne.prime_le_prime_iff_eq
      (by rwa [Ne, Ideal.map_eq_bot_iff_of_injective hf])).mp Ideal.map_comap_le

  refine ⟨{
    toFun := fun ⟨𝔮, h𝔮p, h𝔮ne, h𝔮nc⟩ =>
      ⟨Ideal.comap f 𝔮, Ideal.comap_isPrime f 𝔮, comap_ne_bot 𝔮 h𝔮ne,
       fun h => h𝔮nc (Ideal.map_le_of_le_comap h)⟩
    invFun := fun ⟨𝔭, h𝔭p, h𝔭ne, h𝔭nc⟩ =>
      ⟨Ideal.map f 𝔭,
       @ideal_extension_prime_coprime_conductor O B _ _ _ _ _ _ hf 𝔠 𝔭 h𝔭p h𝔠_cond
         (h_sup 𝔭 h𝔭p h𝔭ne h𝔭nc) h𝔭nc,
       by rwa [Ne, Ideal.map_eq_bot_iff_of_injective hf],
       by rw [Ideal.map_le_iff_le_comap, comap_map_eq 𝔭 h𝔭p h𝔭nc]; exact h𝔭nc⟩
    left_inv := fun ⟨𝔮, h𝔮p, h𝔮ne, h𝔮nc⟩ =>
      Subtype.ext (map_comap_eq 𝔮 h𝔮p h𝔮ne h𝔮nc)
    right_inv := fun ⟨𝔭, h𝔭p, h𝔭ne, h𝔭nc⟩ =>
      Subtype.ext (comap_map_eq 𝔭 h𝔭p h𝔭nc)
  },
  fun ⟨𝔮, h𝔮p, h𝔮ne, h𝔮nc⟩ => rfl,
  fun ⟨𝔭, h𝔭p, h𝔭ne, h𝔭nc⟩ => by simp [Equiv.coe_fn_symm_mk]⟩


theorem extendedHom_isPrimeTo_of_comap
    {O : Type*} {B : Type*}
    [CommRing O] [IsDomain O] [IsNoetherianRing O]
    [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra O B]
    (hf : Function.Injective (algebraMap O B))
    (𝔠 : Ideal B)
    (h𝔠_cond : ∀ c ∈ 𝔠, ∀ b : B, c * b ∈ (algebraMap O B).range)
    (hle : (nonZeroDivisors O) ≤ Submonoid.comap (algebraMap O B) (nonZeroDivisors B))
    (u : (FractionalIdeal (nonZeroDivisors O) (Localization (nonZeroDivisors O)))ˣ)
    (hu : (u : FractionalIdeal (nonZeroDivisors O) (Localization (nonZeroDivisors O))).IsPrimeTo
      (𝔠.comap (algebraMap O B))) :
    ((Units.map (FractionalIdeal.extendedHom (Localization (nonZeroDivisors B)) hle).toMonoidHom u :
      FractionalIdeal (nonZeroDivisors B) (Localization (nonZeroDivisors B))).IsPrimeTo 𝔠) := by
  intro 𝔮 h𝔮_prime h𝔮_ge

  set 𝔭 := 𝔮.comap (algebraMap O B) with h𝔭_def

  haveI h𝔭_prime : 𝔭.IsPrime := h𝔮_prime.comap (algebraMap O B)

  have h𝔭_ge : 𝔠.comap (algebraMap O B) ≤ 𝔭 := Ideal.comap_mono h𝔮_ge

  have hu_at_𝔭 := hu 𝔭 h𝔭_ge

  have hu_inv : ((↑u⁻¹ : FractionalIdeal (nonZeroDivisors O) (Localization (nonZeroDivisors O))).IsPrimeTo
      (𝔠.comap (algebraMap O B))) :=
    (invertibleFractionalIdealsPrimeTo (𝔠.comap (algebraMap O B))).inv_mem' hu
  have hu_inv_at_𝔭 := hu_inv 𝔭 h𝔭_ge

  set A := FractionalIdeal.extended (Localization (nonZeroDivisors B))
    (nonZeroDivisors_le_comap_atPrime 𝔮)
    ((FractionalIdeal.extendedHom (Localization (nonZeroDivisors B)) hle) u.val)
  set B' := FractionalIdeal.extended (Localization (nonZeroDivisors B))
    (nonZeroDivisors_le_comap_atPrime 𝔮)
    ((FractionalIdeal.extendedHom (Localization (nonZeroDivisors B)) hle) u⁻¹.val)

  have hAB : A * B' = 1 := by
    rw [← FractionalIdeal.extended_mul, ← map_mul, Units.mul_inv]
    simp only [map_one]
    exact FractionalIdeal.extended_one _ _


  have hψ_eq_id : IsLocalization.map (Localization (nonZeroDivisors O))
      (algebraMap O (Localization.AtPrime 𝔭)) (nonZeroDivisors_le_comap_atPrime 𝔭) =
      RingHom.id _ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors O)
    ext a
    simp only [RingHom.comp_apply, IsLocalization.map_eq, RingHom.id_apply]
    exact (IsScalarTower.algebraMap_apply O (Localization.AtPrime 𝔭)
      (Localization (nonZeroDivisors O)) a).symm

  have hχ_eq_id : IsLocalization.map (Localization (nonZeroDivisors B))
      (algebraMap B (Localization.AtPrime 𝔮)) (nonZeroDivisors_le_comap_atPrime 𝔮) =
      RingHom.id _ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors B)
    ext a
    simp only [RingHom.comp_apply, IsLocalization.map_eq, RingHom.id_apply]
    exact (IsScalarTower.algebraMap_apply B (Localization.AtPrime 𝔮)
      (Localization (nonZeroDivisors B)) a).symm


  set φ := IsLocalization.map (S := Localization (nonZeroDivisors O)) (Localization (nonZeroDivisors B)) (algebraMap O B) hle
  have hfactor : ∀ a : Localization.AtPrime 𝔭,
      φ (algebraMap (Localization.AtPrime 𝔭) (Localization (nonZeroDivisors O)) a) =
      algebraMap (Localization.AtPrime 𝔮) (Localization (nonZeroDivisors B))
        (Localization.localRingHom 𝔭 𝔮 (algebraMap O B) h𝔭_def a) := by


    suffices h : (φ.comp (algebraMap (Localization.AtPrime 𝔭) (Localization (nonZeroDivisors O)))) =
        ((algebraMap (Localization.AtPrime 𝔮) (Localization (nonZeroDivisors B))).comp
          (Localization.localRingHom 𝔭 𝔮 (algebraMap O B) h𝔭_def)) from
      fun a => congr_fun (congr_arg DFunLike.coe h) a
    apply IsLocalization.ringHom_ext 𝔭.primeCompl
    ext a
    simp only [RingHom.comp_apply]


    rw [← IsScalarTower.algebraMap_apply O (Localization.AtPrime 𝔭) (Localization (nonZeroDivisors O)),
        IsLocalization.map_eq]
    rw [Localization.localRingHom_to_map,
        ← IsScalarTower.algebraMap_apply B (Localization.AtPrime 𝔮) (Localization (nonZeroDivisors B))]


  have htransfer : ∀ I : FractionalIdeal (nonZeroDivisors O) (Localization (nonZeroDivisors O)),
      ∀ x ∈ Submodule.span (Localization.AtPrime 𝔭)
        (IsLocalization.map (Localization (nonZeroDivisors O))
          (algebraMap O (Localization.AtPrime 𝔭)) (nonZeroDivisors_le_comap_atPrime 𝔭) '' (SetLike.coe I)),
      φ x ∈ Submodule.span (Localization.AtPrime 𝔮) (φ '' (SetLike.coe I)) := by
    intro I x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨y, hy, rfl⟩
      rw [hψ_eq_id, RingHom.id_apply]
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    · simp [map_zero]
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx_mem
      rw [Algebra.smul_def, map_mul, hfactor]
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hx_mem

  have h1A : 1 ≤ A := by
    rw [FractionalIdeal.one_le]


    have hu_one : (1 : Localization (nonZeroDivisors O)) ∈
        FractionalIdeal.extended (Localization (nonZeroDivisors O))
          (nonZeroDivisors_le_comap_atPrime 𝔭) u.val :=
      hu_at_𝔭 ▸ FractionalIdeal.one_le.mp le_rfl
    rw [FractionalIdeal.mem_extended_iff] at hu_one


    have h1_in_span : φ 1 ∈ Submodule.span (Localization.AtPrime 𝔮) (φ '' ↑u.val) :=
      htransfer u.val 1 hu_one
    rw [map_one] at h1_in_span


    show (1 : Localization (nonZeroDivisors B)) ∈ (A : Submodule (Localization.AtPrime 𝔮) (Localization (nonZeroDivisors B)))
    rw [FractionalIdeal.coe_extended_eq_span]
    apply Submodule.span_mono _ h1_in_span
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨φ y, ?_, ?_⟩
    ·
      show φ y ∈ (FractionalIdeal.extendedHom (Localization (nonZeroDivisors B)) hle u.val :
        FractionalIdeal (nonZeroDivisors B) (Localization (nonZeroDivisors B)))
      rw [FractionalIdeal.extendedHom_apply, FractionalIdeal.mem_extended_iff]
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    ·
      have : (IsLocalization.map (Localization (nonZeroDivisors B))
        (algebraMap B (Localization.AtPrime 𝔮)) (nonZeroDivisors_le_comap_atPrime 𝔮)) (φ y) = φ y := by
        rw [hχ_eq_id]; rfl
      exact this

  have h1B : 1 ≤ B' := by
    rw [FractionalIdeal.one_le]
    have hu_inv_one : (1 : Localization (nonZeroDivisors O)) ∈
        FractionalIdeal.extended (Localization (nonZeroDivisors O))
          (nonZeroDivisors_le_comap_atPrime 𝔭) u⁻¹.val :=
      hu_inv_at_𝔭 ▸ FractionalIdeal.one_le.mp le_rfl
    rw [FractionalIdeal.mem_extended_iff] at hu_inv_one
    have h1_in_span : φ 1 ∈ Submodule.span (Localization.AtPrime 𝔮) (φ '' ↑u⁻¹.val) :=
      htransfer u⁻¹.val 1 hu_inv_one
    rw [map_one] at h1_in_span
    show (1 : Localization (nonZeroDivisors B)) ∈ (B' : Submodule (Localization.AtPrime 𝔮) (Localization (nonZeroDivisors B)))
    rw [FractionalIdeal.coe_extended_eq_span]
    apply Submodule.span_mono _ h1_in_span
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨φ y, ?_, ?_⟩
    · show φ y ∈ (FractionalIdeal.extendedHom (Localization (nonZeroDivisors B)) hle u⁻¹.val :
        FractionalIdeal (nonZeroDivisors B) (Localization (nonZeroDivisors B)))
      rw [FractionalIdeal.extendedHom_apply, FractionalIdeal.mem_extended_iff]
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    · have : (IsLocalization.map (Localization (nonZeroDivisors B))
        (algebraMap B (Localization.AtPrime 𝔮)) (nonZeroDivisors_le_comap_atPrime 𝔮)) (φ y) = φ y := by
        rw [hχ_eq_id]; rfl
      exact this


  have hB_le_1 : B' ≤ 1 := by
    calc B' = 1 * B' := (one_mul B').symm
    _ ≤ A * B' := mul_le_mul_left h1A B'
    _ = 1 := hAB
  have hB_eq_1 : B' = 1 := le_antisymm hB_le_1 h1B
  calc A = A * 1 := (mul_one A).symm
  _ = A * B' := by rw [hB_eq_1]
  _ = 1 := hAB






theorem coprime_residue_field_iso
    {A : Type*} {O : Type*} {B : Type*}
    [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [CommRing O] [IsDomain O]
    [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A O] [Algebra A B] [Algebra O B]
    [IsScalarTower A O B]
    (𝔮 : Ideal B) [h𝔮 : 𝔮.IsPrime] (h𝔮_ne : 𝔮 ≠ ⊥)
    (𝔠 : Ideal B) (h𝔮_cond : ¬ 𝔠 ≤ 𝔮)

    (h_conductor : ∀ (c : B), c ∈ 𝔠 → ∀ (b : B), ∃ (o : O), algebraMap O B o = c * b) :
    Nonempty (B ⧸ 𝔮 ≃+* O ⧸ (𝔮.comap (algebraMap O B))) := by

  let φ := Ideal.quotientMap 𝔮 (algebraMap O B) (le_refl _)
  have hφ_inj : Function.Injective φ := Ideal.quotientMap_injective
  have hφ_surj : Function.Surjective φ := by

    obtain ⟨s, hs_mem, hs_notin⟩ := Set.not_subset.mp h𝔮_cond
    haveI h𝔮_max : 𝔮.IsMaximal := h𝔮.isMaximal h𝔮_ne

    have hs_coprime : Ideal.span {s} ⊔ 𝔮 = ⊤ := by
      have h1 : 𝔮 < Ideal.span {s} ⊔ 𝔮 :=
        lt_of_le_of_ne le_sup_right (fun h =>
          hs_notin (h ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self s)))
      exact h𝔮_max.1.2 _ h1

    have h1 : (1 : B) ∈ Ideal.span {s} ⊔ 𝔮 := hs_coprime ▸ Submodule.mem_top
    rw [Submodule.mem_sup] at h1
    obtain ⟨x, hx, q₀, hq₀, hxq⟩ := h1
    rw [Ideal.mem_span_singleton] at hx
    obtain ⟨a₀, rfl⟩ := hx


    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y

    obtain ⟨o, ho⟩ := h_conductor s hs_mem (b * a₀)
    refine ⟨Ideal.Quotient.mk _ o, ?_⟩
    simp only [φ, Ideal.quotientMap_mk]
    rw [Ideal.Quotient.eq]


    have hkey : algebraMap O B o - b = -(b * q₀) := by
      have h1 : s * a₀ = 1 - q₀ := by linear_combination hxq
      calc algebraMap O B o - b = s * (b * a₀) - b := by rw [ho]
        _ = b * (s * a₀) - b := by ring_nf
        _ = b * (1 - q₀) - b := by rw [h1]
        _ = -(b * q₀) := by ring
    rw [hkey]
    exact 𝔮.neg_mem (𝔮.mul_mem_left b hq₀)
  exact ⟨(RingEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩).symm⟩

theorem coprime_residue_degree_eq
    {A : Type*} {O : Type*} {B : Type*}
    [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [CommRing O] [IsDomain O]
    [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A O] [Algebra A B] [Algebra O B]
    [IsScalarTower A O B]
    (𝔮 : Ideal B) [h𝔮 : 𝔮.IsPrime] (h𝔮_ne : 𝔮 ≠ ⊥)
    (𝔠 : Ideal B) (h𝔮_cond : ¬ 𝔠 ≤ 𝔮)
    (h_conductor : ∀ (c : B), c ∈ 𝔠 → ∀ (b : B), ∃ (o : O), algebraMap O B o = c * b) :
    Nat.card (B ⧸ 𝔮) = Nat.card (O ⧸ 𝔮.comap (algebraMap O B)) := by
  obtain ⟨e⟩ := coprime_residue_field_iso (A := A) 𝔮 h𝔮_ne 𝔠 h𝔮_cond h_conductor
  exact Nat.card_congr e.toEquiv

theorem coprime_ideal_norm_eq
    {A : Type*} {O : Type*} {B : Type*}
    [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [CommRing O] [IsDomain O]
    [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A O] [Algebra A B] [Algebra O B]
    [IsScalarTower A O B]
    (𝔮 : Ideal B) [h𝔮 : 𝔮.IsPrime] (h𝔮_ne : 𝔮 ≠ ⊥)
    (𝔠 : Ideal B) (h𝔮_cond : ¬ 𝔠 ≤ 𝔮)
    (h_conductor : ∀ (c : B), c ∈ 𝔠 → ∀ (b : B), ∃ (o : O), algebraMap O B o = c * b) :
    Submodule.cardQuot (𝔮 : Submodule B B) =
      Submodule.cardQuot ((𝔮.comap (algebraMap O B)) : Submodule O O) := by
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  obtain ⟨e⟩ := coprime_residue_field_iso (A := A) 𝔮 h𝔮_ne 𝔠 h𝔮_cond h_conductor
  exact Nat.card_congr e.toEquiv

theorem spanNorm_le_of_conductor_coprime
    {A : Type*} {O : Type*} {B : Type*}
    [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [CommRing O] [IsDomain O]
    [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A O] [Algebra A B] [Algebra O B]
    [IsScalarTower A O B]
    [Module.Finite A B]
    [Module.IsTorsionFree A B]
    (𝔮 : Ideal B) [h𝔮 : 𝔮.IsPrime] (h𝔮_ne : 𝔮 ≠ ⊥)
    (𝔠 : Ideal B) (_h𝔮_cond : ¬ 𝔠 ≤ 𝔮)
    (h_conductor : ∀ (c : B), c ∈ 𝔠 → ∀ (b : B), ∃ (o : O), algebraMap O B o = c * b)
    (h_cond_A : ¬ (𝔠.comap (algebraMap A B) ≤ 𝔮.comap (algebraMap A B))) :
    Ideal.spanNorm A 𝔮 ≤
      Ideal.span (Set.image (Algebra.intNorm A B)
        (Set.image (algebraMap O B) (↑(𝔮.comap (algebraMap O B)) : Set O))) := by
  set J := Ideal.span (Set.image (Algebra.intNorm A B)
    (Set.image (algebraMap O B) (↑(𝔮.comap (algebraMap O B)) : Set O))) with hJ_def
  set 𝔭₀ := 𝔮.comap (algebraMap A B) with h𝔭₀_def
  letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
  have hinj_AK : Function.Injective (algebraMap A (FractionRing A)) :=
    IsFractionRing.injective A (FractionRing A)
  have intNorm_alg : ∀ (a : A),
      Algebra.intNorm A B (algebraMap A B a) =
        a ^ Module.finrank (FractionRing A) (FractionRing B) := by
    intro a; apply hinj_AK
    rw [map_pow, Algebra.algebraMap_intNorm_fractionRing,
        show (algebraMap B (FractionRing B)) ((algebraMap A B) a) =
          (algebraMap (FractionRing A) (FractionRing B)) ((algebraMap A (FractionRing A)) a) from by
        rw [← IsScalarTower.algebraMap_apply A B (FractionRing B),
            ← IsScalarTower.algebraMap_apply A (FractionRing A) (FractionRing B)],
        Algebra.norm_algebraMap]
  have h𝔭₀_prime : 𝔭₀.IsPrime := Ideal.IsPrime.comap (algebraMap A B)
  have h𝔭₀_ne_bot : 𝔭₀ ≠ ⊥ := by
    haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔮_ne
    exact Ideal.comap_ne_bot_of_integral_mem hx_ne hx_mem (Algebra.IsIntegral.isIntegral x)
  have h𝔭₀_max : 𝔭₀.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h𝔭₀_ne_bot h𝔭₀_prime

  apply Ideal.le_of_localization_maximal
  intro P hP
  by_cases hne : 𝔭₀ = P
  ·
    subst hne
    obtain ⟨s, hs_in_cond, hs_not_in_p0⟩ := Set.not_subset.mp h_cond_A
    set locMap := algebraMap A (Localization.AtPrime 𝔭₀) with hlocMap_def
    rw [Ideal.map_le_iff_le_comap, Ideal.spanNorm, Ideal.map]
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_image, SetLike.mem_coe] at hx
    obtain ⟨b, hb_in_𝔮, rfl⟩ := hx
    rw [SetLike.mem_coe, Ideal.mem_comap]

    obtain ⟨o, ho⟩ := h_conductor (algebraMap A B s) hs_in_cond b
    have h_o_mem : o ∈ 𝔮.comap (algebraMap O B) := by
      rw [Ideal.mem_comap, ho]; exact 𝔮.mul_mem_left _ hb_in_𝔮
    have h_norm_o_in_J : Algebra.intNorm A B (algebraMap O B o) ∈ J :=
      Ideal.subset_span ⟨algebraMap O B o, ⟨o, h_o_mem, rfl⟩, rfl⟩

    have h_norm_eq : Algebra.intNorm A B (algebraMap O B o) =
        Algebra.intNorm A B (algebraMap A B s) * Algebra.intNorm A B b := by
      rw [ho, map_mul]
    rw [h_norm_eq] at h_norm_o_in_J

    have h_unit : IsUnit (locMap (Algebra.intNorm A B (algebraMap A B s))) :=
      IsLocalization.map_units (Localization.AtPrime 𝔭₀)
        ⟨_, show Algebra.intNorm A B (algebraMap A B s) ∈ 𝔭₀.primeCompl from by
              rw [intNorm_alg]; exact mt (h𝔭₀_prime.mem_of_pow_mem _) hs_not_in_p0⟩

    exact (Ideal.unit_mul_mem_iff_mem (J.map locMap) h_unit).mp
      (by rw [← map_mul]; exact Ideal.mem_map_of_mem _ h_norm_o_in_J)
  ·
    have hP_prime := Ideal.IsMaximal.isPrime hP
    obtain ⟨a, ha_in_p0, ha_not_in_P⟩ :=
      Set.not_subset.mp (fun h => absurd (h𝔭₀_max.eq_of_le hP.ne_top h) hne)
    have h_a_mem_O : algebraMap A O a ∈ 𝔮.comap (algebraMap O B) := by
      rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply A O B]; exact (ha_in_p0 : _)
    have ha_in_J : Algebra.intNorm A B (algebraMap A B a) ∈ J :=
      Ideal.subset_span ⟨algebraMap O B (algebraMap A O a), ⟨algebraMap A O a, h_a_mem_O, rfl⟩,
        by rw [IsScalarTower.algebraMap_apply A O B]⟩
    rw [show J.map (algebraMap A (Localization.AtPrime P)) = ⊤ from
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha_in_J)
        (IsLocalization.map_units (Localization.AtPrime P)
          ⟨_, show Algebra.intNorm A B (algebraMap A B a) ∈ P.primeCompl from by
                rw [intNorm_alg]; exact mt (hP_prime.mem_of_pow_mem _) ha_not_in_P⟩)]
    exact le_top

theorem coprime_norm_commutes
    {A : Type*} {O : Type*} {B : Type*}
    [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [CommRing O] [IsDomain O]
    [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A O] [Algebra A B] [Algebra O B]
    [IsScalarTower A O B]
    [Module.Finite A B]
    [Module.IsTorsionFree A B]
    (𝔮 : Ideal B) [h𝔮 : 𝔮.IsPrime] (h𝔮_ne : 𝔮 ≠ ⊥)
    (𝔠 : Ideal B) (h𝔮_cond : ¬ 𝔠 ≤ 𝔮)
    (h_conductor : ∀ (c : B), c ∈ 𝔠 → ∀ (b : B), ∃ (o : O), algebraMap O B o = c * b)
    (h_cond_A : ¬ (𝔠.comap (algebraMap A B) ≤ 𝔮.comap (algebraMap A B))) :


    Ideal.spanNorm A 𝔮 =
      Ideal.span (Set.image (Algebra.intNorm A B)
        (Set.image (algebraMap O B) (↑(𝔮.comap (algebraMap O B)) : Set O))) := by
  apply le_antisymm
  ·
    exact spanNorm_le_of_conductor_coprime 𝔮 h𝔮_ne 𝔠 h𝔮_cond h_conductor h_cond_A
  ·
    apply Ideal.span_le.mpr
    intro a ha
    simp only [Set.mem_image, SetLike.mem_coe] at ha
    obtain ⟨_, ⟨o, ho, rfl⟩, rfl⟩ := ha
    exact Ideal.intNorm_mem_spanNorm A (Ideal.mem_comap.mp ho)

theorem order_coprime_prime_properties
    {A : Type*} {O : Type*} {B : Type*}
    [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [CommRing O] [IsDomain O]
    [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A O] [Algebra A B] [Algebra O B]
    [IsScalarTower A O B]
    [Module.Finite A B]
    [Module.IsTorsionFree A B]
    [PerfectField (FractionRing A)]
    (𝔮 : Ideal B) [h𝔮 : 𝔮.IsPrime] (h𝔮_ne : 𝔮 ≠ ⊥)
    (𝔠 : Ideal B) (h𝔮_cond : ¬ 𝔠 ≤ 𝔮)
    (h_conductor : ∀ (c : B), c ∈ 𝔠 → ∀ (b : B), ∃ (o : O), algebraMap O B o = c * b)
    (h_ext : 𝔠 = Ideal.map (algebraMap A B) (𝔠.comap (algebraMap A B))) :

    Nat.card (B ⧸ 𝔮) = Nat.card (O ⧸ 𝔮.comap (algebraMap O B)) ∧

    Submodule.cardQuot (𝔮 : Submodule B B) =
      Submodule.cardQuot ((𝔮.comap (algebraMap O B)) : Submodule O O) ∧

    Ideal.spanNorm A 𝔮 =
      Ideal.span (Set.image (Algebra.intNorm A B)
        (Set.image (algebraMap O B) (↑(𝔮.comap (algebraMap O B)) : Set O))) ∧

    Ideal.spanNorm A 𝔮 =
      (𝔮.comap (algebraMap A B)) ^ (𝔮.comap (algebraMap A B)).inertiaDeg 𝔮 := by


  have h_cond_A : ¬ (𝔠.comap (algebraMap A B) ≤ 𝔮.comap (algebraMap A B)) := by
    intro h_contra
    exact h𝔮_cond (calc
      𝔠 = Ideal.map (algebraMap A B) (𝔠.comap (algebraMap A B)) := h_ext
      _ ≤ Ideal.map (algebraMap A B) (𝔮.comap (algebraMap A B)) := Ideal.map_mono h_contra
      _ ≤ 𝔮 := Ideal.map_comap_le)
  refine ⟨coprime_residue_degree_eq (A := A) 𝔮 h𝔮_ne 𝔠 h𝔮_cond h_conductor,
    coprime_ideal_norm_eq (A := A) 𝔮 h𝔮_ne 𝔠 h𝔮_cond h_conductor,
    coprime_norm_commutes 𝔮 h𝔮_ne 𝔠 h𝔮_cond h_conductor h_cond_A, ?_⟩
  haveI := h𝔮.isMaximal h𝔮_ne
  haveI := (h𝔮.under A).isMaximal (Ideal.under_ne_bot A h𝔮_ne)
  rw [Ideal.spanNorm_eq]
  exact Ideal.relNorm_eq_pow_of_isMaximal 𝔮 (𝔮.comap (algebraMap A B))

end FaithfulStatements
