/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring

noncomputable section

open IsDedekindDomain

set_option linter.unusedSectionVars false

def ExtendsValuation
    (A : Type*) [CommRing A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L]
    (𝔭 : HeightOneSpectrum A)
    (w : Valuation L (WithZero (Multiplicative ℤ))) : Prop :=
  (w.comap (algebraMap K L)).IsEquiv (𝔭.valuation K)

section AKLB

variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [Algebra A L] [IsScalarTower A K L]
variable (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B]
         [Algebra A B] [Algebra B L] [IsScalarTower A B L]
         [IsIntegralClosure B A L] [IsFractionRing B L]

def primesAbove (𝔭 : HeightOneSpectrum A) : Set (HeightOneSpectrum B) :=
  { 𝔮 : HeightOneSpectrum B | 𝔮.asIdeal.LiesOver 𝔭.asIdeal }

lemma mem_of_liesOver (𝔭 : HeightOneSpectrum A) (𝔮 : HeightOneSpectrum B)
    (hlo : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) (a : A) :
    a ∈ 𝔭.asIdeal ↔ algebraMap A B a ∈ 𝔮.asIdeal := by
  rw [hlo.over]; exact Ideal.mem_comap

set_option maxHeartbeats 800000 in
theorem valuation_extends_of_liesOver
    (𝔭 : HeightOneSpectrum A) (𝔮 : HeightOneSpectrum B)
    (hlo : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) :
    ExtendsValuation A K L 𝔭 (𝔮.valuation L) := by


  rw [ExtendsValuation, Valuation.isEquiv_iff_val_le_one]
  intro x

  obtain ⟨n, d, hnd⟩ := 𝔭.exists_primeCompl_mul_eq_or_mul_eq (K := K) x

  have hd_𝔭 : (d : A) ∉ 𝔭.asIdeal := d.prop
  have hd_𝔮 : algebraMap A B (d : A) ∉ 𝔮.asIdeal :=
    (mem_of_liesOver A B 𝔭 𝔮 hlo _).not.mp hd_𝔭

  have hvd_𝔭 : 𝔭.valuation K (algebraMap A K (d : A)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hd_𝔭
  have hvd_𝔮 : 𝔮.valuation L (algebraMap K L (algebraMap A K (d : A))) = 1 := by
    simp only [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
      HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff.mpr hd_𝔮]

  have hvn_𝔭 : 𝔭.valuation K (algebraMap A K n) ≤ 1 := HeightOneSpectrum.valuation_le_one 𝔭 n
  have hvn_𝔮 : 𝔮.valuation L (algebraMap K L (algebraMap A K n)) ≤ 1 := by
    simp only [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one 𝔮 (algebraMap A B n)
  simp only [Valuation.comap_apply]
  cases hnd with
  | inl hnd =>

    constructor <;> intro _
    · have h1 : 𝔭.valuation K x * 𝔭.valuation K (algebraMap A K (d : A)) =
          𝔭.valuation K (algebraMap A K n) := by rw [← Valuation.map_mul, hnd]
      rw [hvd_𝔭, mul_one] at h1; rw [h1]; exact hvn_𝔭
    · have h1 : 𝔮.valuation L (algebraMap K L x) *
          𝔮.valuation L (algebraMap K L (algebraMap A K (d : A))) =
          𝔮.valuation L (algebraMap K L (algebraMap A K n)) := by
        rw [← Valuation.map_mul, ← map_mul, hnd]
      rw [hvd_𝔮, mul_one] at h1; rw [h1]; exact hvn_𝔮
  | inr hnd =>

    have hmul_𝔭 : 𝔭.valuation K x * 𝔭.valuation K (algebraMap A K n) = 1 := by
      rw [← Valuation.map_mul, hnd, hvd_𝔭]
    have hmul_𝔮 : 𝔮.valuation L (algebraMap K L x) *
        𝔮.valuation L (algebraMap K L (algebraMap A K n)) = 1 := by
      rw [← Valuation.map_mul, ← map_mul, hnd, hvd_𝔮]
    have h𝔭 : 𝔭.valuation K x ≤ 1 ↔ 𝔭.valuation K (algebraMap A K n) = 1 := by
      constructor
      · intro ha; exact eq_one_of_one_le_mul_right ha hvn_𝔭 (hmul_𝔭 ▸ le_refl _)
      · intro hb; rw [hb, mul_one] at hmul_𝔭; rw [hmul_𝔭]
    have h𝔮 : 𝔮.valuation L (algebraMap K L x) ≤ 1 ↔
        𝔮.valuation L (algebraMap K L (algebraMap A K n)) = 1 := by
      constructor
      · intro ha; exact eq_one_of_one_le_mul_right ha hvn_𝔮 (hmul_𝔮 ▸ le_refl _)
      · intro hb; rw [hb, mul_one] at hmul_𝔮; rw [hmul_𝔮]

    rw [h𝔮, h𝔭]
    simp only [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact (mem_of_liesOver A B 𝔭 𝔮 hlo n).not.symm

set_option maxHeartbeats 800000 in
theorem dvr_overring_equiv
    {B' : Type*} [CommRing B'] [IsDomain B'] [IsDedekindDomain B']
    {L' : Type*} [Field L'] [Algebra B' L'] [IsFractionRing B' L']
    (𝔮 : HeightOneSpectrum B')
    (w : Valuation L' (WithZero (Multiplicative ℤ)))
    (hB : ∀ b : B', w (algebraMap B' L' b) ≤ 1)
    (hIdeal : ∀ b : B', b ∈ 𝔮.asIdeal ↔ w (algebraMap B' L' b) < 1) :
    (𝔮.valuation L').IsEquiv w := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  obtain ⟨n, d, hnd⟩ := 𝔮.exists_primeCompl_mul_eq_or_mul_eq (K := L') x
  have hd_not_mem : (d : B') ∉ 𝔮.asIdeal := d.prop
  have hw_d_eq_one : w (algebraMap B' L' (d : B')) = 1 :=
    le_antisymm (hB d) (not_lt.mp (fun h => hd_not_mem ((hIdeal d).mpr h)))
  have hv_d_eq_one : 𝔮.valuation L' (algebraMap B' L' (d : B')) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hd_not_mem
  have hw_n_le : w (algebraMap B' L' n) ≤ 1 := hB n
  have hv_n_le : 𝔮.valuation L' (algebraMap B' L' n) ≤ 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one 𝔮 n
  cases hnd with
  | inl hnd =>

    constructor <;> intro _
    · have h1 : w x * w (algebraMap B' L' (d : B')) =
          w (algebraMap B' L' n) := by rw [← Valuation.map_mul, hnd]
      rw [hw_d_eq_one, mul_one] at h1; rw [h1]; exact hw_n_le
    · have h1 : 𝔮.valuation L' x * 𝔮.valuation L' (algebraMap B' L' (d : B')) =
          𝔮.valuation L' (algebraMap B' L' n) := by rw [← Valuation.map_mul, hnd]
      rw [hv_d_eq_one, mul_one] at h1; rw [h1]; exact hv_n_le
  | inr hnd =>

    have hmul_v : 𝔮.valuation L' x * 𝔮.valuation L' (algebraMap B' L' n) = 1 := by
      rw [← Valuation.map_mul, hnd, hv_d_eq_one]
    have hmul_w : w x * w (algebraMap B' L' n) = 1 := by
      rw [← Valuation.map_mul, hnd, hw_d_eq_one]
    have hv_iff : 𝔮.valuation L' x ≤ 1 ↔ 𝔮.valuation L' (algebraMap B' L' n) = 1 := by
      constructor
      · intro ha; exact eq_one_of_one_le_mul_right ha hv_n_le (hmul_v ▸ le_refl _)
      · intro hb; rw [hb, mul_one] at hmul_v; rw [hmul_v]
    have hw_iff : w x ≤ 1 ↔ w (algebraMap B' L' n) = 1 := by
      constructor
      · intro ha; exact eq_one_of_one_le_mul_right ha hw_n_le (hmul_w ▸ le_refl _)
      · intro hb; rw [hb, mul_one] at hmul_w; rw [hmul_w]
    rw [hv_iff, hw_iff]

    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    constructor
    · intro h; exact le_antisymm (hB n) (not_lt.mp (fun hlt => h ((hIdeal n).mpr hlt)))
    · intro h hn; exact absurd ((hIdeal n).mp hn) (not_lt.mpr (ge_of_eq h))

set_option maxHeartbeats 800000 in
theorem valuation_surjective_of_extends
    (𝔭 : HeightOneSpectrum A)
    (w : Valuation L (WithZero (Multiplicative ℤ)))
    (hw : ExtendsValuation A K L 𝔭 w) :
    ∃ 𝔮 : HeightOneSpectrum B,
      𝔮 ∈ primesAbove A B 𝔭 ∧ (𝔮.valuation L).IsEquiv w := by

  have hA : ∀ a : A, w (algebraMap A L a) ≤ 1 := by
    intro a; rw [IsScalarTower.algebraMap_apply A K L]
    have h := (Valuation.isEquiv_iff_val_le_one.mp hw).mpr (HeightOneSpectrum.valuation_le_one 𝔭 a)
    simpa [Valuation.comap_apply] using h

  have hB : ∀ b : B, w (algebraMap B L b) ≤ 1 := by
    intro b
    let φ : A →+* w.valuationSubring :=
      (algebraMap A L).codRestrict w.valuationSubring.toSubring (fun a => hA a)
    have hbL_int : IsIntegral w.valuationSubring (algebraMap B L b) :=
      IsIntegral.map_of_comp_eq φ (algebraMap B L)
        (by ext a; simp [φ, RingHom.codRestrict, ← IsScalarTower.algebraMap_apply A B L])
        (IsIntegralClosure.isIntegral A L b)
    obtain ⟨⟨y, hy_mem⟩, hy_eq⟩ := IsIntegrallyClosed.isIntegral_iff.mp hbL_int
    rw [show algebraMap w.valuationSubring L ⟨y, hy_mem⟩ = y from rfl] at hy_eq
    rw [← hy_eq]; exact hy_mem

  let I : Ideal B := {
    carrier := {b : B | w (algebraMap B L b) < 1}
    add_mem' := by
      intro a b ha hb; simp only [Set.mem_setOf_eq] at *
      calc w (algebraMap B L (a + b))
          = w (algebraMap B L a + algebraMap B L b) := by rw [map_add]
        _ ≤ max (w (algebraMap B L a)) (w (algebraMap B L b)) := w.map_add _ _
        _ < 1 := max_lt ha hb
    zero_mem' := by simp [Valuation.map_zero]
    smul_mem' := by
      intro c b hb; simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
      calc w (algebraMap B L c) * w (algebraMap B L b)
          ≤ 1 * w (algebraMap B L b) := mul_le_mul_left (hB c) _
        _ = w (algebraMap B L b) := one_mul _
        _ < 1 := hb
  }
  have hI_mem : ∀ b : B, b ∈ I ↔ w (algebraMap B L b) < 1 := fun _ => Iff.rfl

  have hI_prime : I.IsPrime := by
    constructor
    · intro h; have := (hI_mem 1).mp (by rw [h]; trivial); simp at this
    · intro a b hab
      rw [hI_mem] at hab ⊢ ⊢; simp only [map_mul] at hab
      by_contra hc; simp only [not_or] at hc
      have ha1 := le_antisymm (hB a) (not_lt.mp (fun h => hc.1 ((hI_mem a).mpr h)))
      have hb1 := le_antisymm (hB b) (not_lt.mp (fun h => hc.2 ((hI_mem b).mpr h)))
      rw [ha1, hb1, mul_one] at hab; exact lt_irrefl 1 hab

  have hI_ne_bot : I ≠ ⊥ := by
    intro hI_eq
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot 𝔭.ne_bot
    have h𝔭w_a : w (algebraMap A L a) < 1 := by
      rw [IsScalarTower.algebraMap_apply A K L]
      have := (Valuation.isEquiv_iff_val_lt_one.mp hw).mpr
        ((HeightOneSpectrum.valuation_lt_one_iff_mem 𝔭 a).mpr ha)
      simpa [Valuation.comap_apply] using this
    have hAB_in_I : algebraMap A B a ∈ I := by
      rw [hI_mem, ← IsScalarTower.algebraMap_apply A B L]; exact h𝔭w_a
    rw [hI_eq] at hAB_in_I; simp only [Ideal.mem_bot] at hAB_in_I
    have hAB_inj : Function.Injective (algebraMap A B) := by
      intro a₁ a₂ h
      have := congr_arg (algebraMap B L) h
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
      rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L] at this
      exact IsFractionRing.injective A K ((algebraMap K L).injective this)
    exact ha0 (hAB_inj (hAB_in_I.trans (map_zero _).symm))

  let 𝔮 : HeightOneSpectrum B := ⟨I, hI_prime, hI_ne_bot⟩

  have h𝔮_over : 𝔮 ∈ primesAbove A B 𝔭 := by
    simp only [primesAbove, Set.mem_setOf_eq]
    constructor
    ext a
    constructor
    · intro ha
      show w (algebraMap B L (algebraMap A B a)) < 1
      rw [← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L]
      have := (Valuation.isEquiv_iff_val_lt_one.mp hw).mpr
        ((HeightOneSpectrum.valuation_lt_one_iff_mem 𝔭 a).mpr ha)
      simpa [Valuation.comap_apply] using this
    · intro ha
      have : w (algebraMap B L (algebraMap A B a)) < 1 := ha
      rw [← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L] at this
      have h2 : (w.comap (algebraMap K L)) (algebraMap A K a) < 1 := by
        simpa [Valuation.comap_apply] using this
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem 𝔭 a).mp
        ((Valuation.isEquiv_iff_val_lt_one.mp hw).mp h2)

  exact ⟨𝔮, h𝔮_over, dvr_overring_equiv 𝔮 w hB (fun b => hI_mem b)⟩

theorem extending_valuation_bijection_primes_above (𝔭 : HeightOneSpectrum A) :

    (∀ 𝔮₁ 𝔮₂ : HeightOneSpectrum B,
      𝔮₁ ∈ primesAbove A B 𝔭 →
      𝔮₂ ∈ primesAbove A B 𝔭 →
      (𝔮₁.valuation L).IsEquiv (𝔮₂.valuation L) → 𝔮₁ = 𝔮₂) ∧

    (∀ w : Valuation L (WithZero (Multiplicative ℤ)),
      ExtendsValuation A K L 𝔭 w →
      ∃ 𝔮 : HeightOneSpectrum B,
        𝔮 ∈ primesAbove A B 𝔭 ∧ (𝔮.valuation L).IsEquiv w) := by
  constructor
  ·

    intro 𝔮₁ 𝔮₂ _ _ hEquiv
    have hlt : ∀ x : L, (𝔮₁.valuation L) x < 1 ↔ (𝔮₂.valuation L) x < 1 :=
      fun x => (Valuation.isEquiv_iff_val_lt_one.mp hEquiv)
    have hIdeal : 𝔮₁.asIdeal = 𝔮₂.asIdeal := by
      ext r
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) 𝔮₁,
          ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) 𝔮₂]
      exact hlt (algebraMap B L r)
    exact HeightOneSpectrum.ext hIdeal
  ·
    exact valuation_surjective_of_extends A K L B 𝔭

end AKLB

end
