/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.RayClassFields
import Atlas.NumberTheoryI.code.Ideles
import Atlas.NumberTheoryI.code.IdeleNorm
import Atlas.NumberTheoryI.code.KroneckerWeber
import Atlas.NumberTheoryI.code.Cor227
import Atlas.NumberTheoryI.code.Chapter3.FiniteApproximation
import Atlas.NumberTheoryI.code.Ch22NormGroup
import Atlas.NumberTheoryI.code.Prop2219
noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

section ArtinSymbol

universe v

variable (K : Type v) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

def ArtinSymbol
    (𝔔 : Ideal (RingOfIntegers L))
    [𝔔.IsPrime] [Finite (RingOfIntegers L ⧸ 𝔔)] :
    (L ≃ₐ[K] L) :=
  arithFrobAt (RingOfIntegers K) (L ≃ₐ[K] L) 𝔔

theorem ArtinSymbol.isArithFrob
    (𝔔 : Ideal (RingOfIntegers L))
    [𝔔.IsPrime] [Finite (RingOfIntegers L ⧸ 𝔔)] :
    IsArithFrobAt (RingOfIntegers K) (ArtinSymbol K L 𝔔) 𝔔 :=
  IsArithFrobAt.arithFrobAt (RingOfIntegers K) (L ≃ₐ[K] L) 𝔔

end ArtinSymbol

namespace GlobalCFT

universe u

structure IsCongruenceSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) : Prop where
  contains_ray : RayGroup K 𝔪 ≤ 𝒞


lemma FracIdealsCoprime_subgroup_le (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫) :
    FracIdealsCoprime_subgroup K 𝔫 ≤ FracIdealsCoprime_subgroup K 𝔪 := by
  intro I hI v hv
  apply hI v
  intro h0
  exact absurd (Nat.le_zero.mp (h0 ▸ h (Place.finite v))) hv

noncomputable def FracIdealsCoprime.inclusion (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫) :
    FracIdealsCoprime K 𝔫 →* FracIdealsCoprime K 𝔪 :=
  Subgroup.inclusion (FracIdealsCoprime_subgroup_le K 𝔪 𝔫 h)

lemma IsRayGenerator_inclusion (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (I : FracIdealsCoprime K 𝔫) (hI : IsRayGenerator 𝔫 I) :
    IsRayGenerator 𝔪 (Subgroup.inclusion (FracIdealsCoprime_subgroup_le K 𝔪 𝔫 h) I) := by
  obtain ⟨α, hprinc, hcong, hsign⟩ := hI
  refine ⟨α, ?_, ?_, ?_⟩
  ·
    simp only [Subgroup.coe_inclusion]
    exact hprinc
  ·
    intro v hv
    have hv_n : 𝔫 (Place.finite v) ≠ 0 := by
      intro h0; exact hv (Nat.eq_zero_of_le_zero (h0 ▸ h (Place.finite v)))
    have hle : (𝔪 (Place.finite v) : ℤ) ≤ (𝔫 (Place.finite v) : ℤ) :=
      Int.ofNat_le.mpr (h (Place.finite v))
    calc v.valuation K ((α : K) - 1)
        ≤ ↑(Multiplicative.ofAdd (-(𝔫 (Place.finite v) : ℤ))) := hcong v hv_n
      _ ≤ ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ))) := by
          simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le]
          linarith
  ·
    intro w hw
    exact hsign w (fun h0 => hw (Nat.eq_zero_of_le_zero (h0 ▸ h (Place.infinite w))))

theorem RayGroup.inclusion_le (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫) :
    ∀ x : FracIdealsCoprime K 𝔫,
      x ∈ RayGroup K 𝔫 → (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) x ∈ RayGroup K 𝔪 := by

  intro x hx
  let f := FracIdealsCoprime.inclusion K 𝔪 𝔫 h

  have hmem : f x ∈ Subgroup.map f (RayGroup K 𝔫) := ⟨x, hx, rfl⟩

  rw [show RayGroup K 𝔫 = Subgroup.closure {I | IsRayGenerator 𝔫 I} from rfl,
      MonoidHom.map_closure] at hmem

  have himg_sub : f '' {I | IsRayGenerator 𝔫 I} ⊆ {I | IsRayGenerator 𝔪 I} := by
    rintro _ ⟨I, hI, rfl⟩
    exact IsRayGenerator_inclusion K 𝔪 𝔫 h I hI
  exact Subgroup.closure_mono himg_sub hmem

def CongruenceSubgroupEquiv (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂)) : Prop :=
  ∃ (𝔫 : Modulus K) (h₁ : Modulus.dvd 𝔪₁ 𝔫) (h₂ : Modulus.dvd 𝔪₂ 𝔫),
    Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 h₁) 𝒞₁ =
    Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 h₂) 𝒞₂

theorem congruenceSubgroupEquiv_refl (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) :
    CongruenceSubgroupEquiv K 𝔪 𝔪 𝒞 𝒞 := by
  refine ⟨𝔪, fun v => le_refl _, fun v => le_refl _, rfl⟩

theorem congruenceSubgroupEquiv_symm (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (h : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) :
    CongruenceSubgroupEquiv K 𝔪₂ 𝔪₁ 𝒞₂ 𝒞₁ := by
  obtain ⟨𝔫, h₁, h₂, heq⟩ := h
  exact ⟨𝔫, h₂, h₁, heq.symm⟩

theorem FracIdealsCoprime.inclusion_comp (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 𝔭 : Modulus K) (h₁ : Modulus.dvd 𝔪 𝔫) (h₂ : Modulus.dvd 𝔫 𝔭)
    (h₃ : Modulus.dvd 𝔪 𝔭) :
    ∀ x : FracIdealsCoprime K 𝔭,
      (FracIdealsCoprime.inclusion K 𝔪 𝔫 h₁)
        ((FracIdealsCoprime.inclusion K 𝔫 𝔭 h₂) x) =
      (FracIdealsCoprime.inclusion K 𝔪 𝔭 h₃) x := by
  intro x
  simp only [FracIdealsCoprime.inclusion, Subgroup.inclusion]
  rfl





theorem congruenceSubgroupEquiv_trans (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ 𝔪₃ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (𝒞₃ : Subgroup (FracIdealsCoprime K 𝔪₃))
    (h₁₂ : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂)
    (h₂₃ : CongruenceSubgroupEquiv K 𝔪₂ 𝔪₃ 𝒞₂ 𝒞₃) :
    CongruenceSubgroupEquiv K 𝔪₁ 𝔪₃ 𝒞₁ 𝒞₃ := by
  obtain ⟨𝔫₁₂, h₁_12, h₂_12, heq₁₂⟩ := h₁₂
  obtain ⟨𝔫₂₃, h₂_23, h₃_23, heq₂₃⟩ := h₂₃

  let 𝔫 := Modulus.lcm 𝔫₁₂ 𝔫₂₃
  have hd₁₂_n : Modulus.dvd 𝔫₁₂ 𝔫 := fun v => le_max_left _ _
  have hd₂₃_n : Modulus.dvd 𝔫₂₃ 𝔫 := fun v => le_max_right _ _
  have hd₁_n : Modulus.dvd 𝔪₁ 𝔫 := fun v => le_trans (h₁_12 v) (hd₁₂_n v)
  have hd₂_n₁ : Modulus.dvd 𝔪₂ 𝔫 := fun v => le_trans (h₂_12 v) (hd₁₂_n v)
  have hd₂_n₂ : Modulus.dvd 𝔪₂ 𝔫 := fun v => le_trans (h₂_23 v) (hd₂₃_n v)
  have hd₃_n : Modulus.dvd 𝔪₃ 𝔫 := fun v => le_trans (h₃_23 v) (hd₂₃_n v)
  refine ⟨𝔫, hd₁_n, hd₃_n, ?_⟩


  ext x
  simp only [Subgroup.mem_comap]
  constructor
  · intro hx₁


    have step1 : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₁₂ h₂_12)
        ((FracIdealsCoprime.inclusion K 𝔫₁₂ 𝔫 hd₁₂_n) x) ∈ 𝒞₂ := by
      rw [← Subgroup.mem_comap, ← heq₁₂, Subgroup.mem_comap]
      rw [FracIdealsCoprime.inclusion_comp K 𝔪₁ 𝔫₁₂ 𝔫 h₁_12 hd₁₂_n hd₁_n]
      exact hx₁


    have step1' : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 hd₂_n₁) x ∈ 𝒞₂ := by
      rw [← FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔫₁₂ 𝔫 h₂_12 hd₁₂_n hd₂_n₁]
      exact step1

    have step2 : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₂₃ h₂_23)
        ((FracIdealsCoprime.inclusion K 𝔫₂₃ 𝔫 hd₂₃_n) x) ∈ 𝒞₂ := by
      rw [FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔫₂₃ 𝔫 h₂_23 hd₂₃_n hd₂_n₂]
      exact step1'

    have step3 : (FracIdealsCoprime.inclusion K 𝔪₃ 𝔫₂₃ h₃_23)
        ((FracIdealsCoprime.inclusion K 𝔫₂₃ 𝔫 hd₂₃_n) x) ∈ 𝒞₃ := by
      have : (FracIdealsCoprime.inclusion K 𝔫₂₃ 𝔫 hd₂₃_n) x ∈
          Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₂₃ h₂_23) 𝒞₂ := by
        rw [Subgroup.mem_comap]; exact step2
      rw [heq₂₃] at this
      exact this

    rw [← FracIdealsCoprime.inclusion_comp K 𝔪₃ 𝔫₂₃ 𝔫 h₃_23 hd₂₃_n hd₃_n]
    exact step3

  · intro hx₃

    have step1 : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₂₃ h₂_23)
        ((FracIdealsCoprime.inclusion K 𝔫₂₃ 𝔫 hd₂₃_n) x) ∈ 𝒞₂ := by
      rw [← Subgroup.mem_comap, heq₂₃, Subgroup.mem_comap]
      rw [FracIdealsCoprime.inclusion_comp K 𝔪₃ 𝔫₂₃ 𝔫 h₃_23 hd₂₃_n hd₃_n]
      exact hx₃
    have step1' : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 hd₂_n₂) x ∈ 𝒞₂ := by
      rw [← FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔫₂₃ 𝔫 h₂_23 hd₂₃_n hd₂_n₂]
      exact step1
    have step2 : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₁₂ h₂_12)
        ((FracIdealsCoprime.inclusion K 𝔫₁₂ 𝔫 hd₁₂_n) x) ∈ 𝒞₂ := by
      rw [FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔫₁₂ 𝔫 h₂_12 hd₁₂_n hd₂_n₁]
      exact step1'
    have step3 : (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫₁₂ h₁_12)
        ((FracIdealsCoprime.inclusion K 𝔫₁₂ 𝔫 hd₁₂_n) x) ∈ 𝒞₁ := by
      have : (FracIdealsCoprime.inclusion K 𝔫₁₂ 𝔫 hd₁₂_n) x ∈
          Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₁₂ h₂_12) 𝒞₂ := by
        rw [Subgroup.mem_comap]; exact step2
      rw [← heq₁₂] at this
      exact this

    rw [← FracIdealsCoprime.inclusion_comp K 𝔪₁ 𝔫₁₂ 𝔫 h₁_12 hd₁₂_n hd₁_n]
    exact step3




lemma FracIdealsCoprime.subtype_inclusion (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (x : FracIdealsCoprime K 𝔫) :
    (FracIdealsCoprime_subgroup K 𝔪).subtype
      (FracIdealsCoprime.inclusion K 𝔪 𝔫 h x) =
    (FracIdealsCoprime_subgroup K 𝔫).subtype x := by
  simp only [FracIdealsCoprime.inclusion, Subgroup.inclusion]
  rfl

lemma mem_comap_inclusion_iff_mem_toAmbientSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (x : FracIdealsCoprime K 𝔫) :
    x ∈ Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) 𝒞 ↔
    (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
      𝒞.map (FracIdealsCoprime_subgroup K 𝔪).subtype := by
  rw [Subgroup.mem_comap]
  constructor
  · intro hx
    exact ⟨FracIdealsCoprime.inclusion K 𝔪 𝔫 h x, hx,
      FracIdealsCoprime.subtype_inclusion K 𝔪 𝔫 h x⟩
  · rintro ⟨y, hy, heq⟩
    have hval : FracIdealsCoprime.inclusion K 𝔪 𝔫 h x = y := by
      apply Subtype.ext
      have h1 := FracIdealsCoprime.subtype_inclusion K 𝔪 𝔫 h x
      simp only [Subgroup.coe_subtype] at h1 heq
      exact h1.trans heq.symm
    rw [hval]
    exact hy

theorem isEquiv_to_congruenceSubgroupEquiv (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (h₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
    (h₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
    (h_isEquiv : (⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩ : CongruenceSubgroupPair K).IsEquiv
                  ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩) :
    CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ := by
  set p₁ : CongruenceSubgroupPair K := ⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩
  set p₂ : CongruenceSubgroupPair K := ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩
  set 𝔫 := Modulus.lcm 𝔪₁ 𝔪₂
  have hdvd₁ : Modulus.dvd 𝔪₁ 𝔫 := RayClassField.Modulus.dvd_lcm_left 𝔪₁ 𝔪₂
  have hdvd₂ : Modulus.dvd 𝔪₂ 𝔫 := RayClassField.Modulus.dvd_lcm_right 𝔪₁ 𝔪₂
  refine ⟨𝔫, hdvd₁, hdvd₂, ?_⟩
  ext x
  rw [mem_comap_inclusion_iff_mem_toAmbientSubgroup K 𝔪₁ 𝔫 hdvd₁ 𝒞₁ x]
  rw [mem_comap_inclusion_iff_mem_toAmbientSubgroup K 𝔪₂ 𝔫 hdvd₂ 𝒞₂ x]
  have hx_in_I₁ : (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
      FracIdealsCoprime_subgroup K 𝔪₁ :=
    FracIdealsCoprime_subgroup_le K 𝔪₁ 𝔫 hdvd₁ x.2
  have hx_in_I₂ : (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
      FracIdealsCoprime_subgroup K 𝔪₂ :=
    FracIdealsCoprime_subgroup_le K 𝔪₂ 𝔫 hdvd₂ x.2
  constructor
  · intro hx_amb₁
    have : (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
        FracIdealsCoprime_subgroup K 𝔪₂ ⊓ p₁.toAmbientSubgroup :=
      ⟨hx_in_I₂, hx_amb₁⟩
    rw [← h_isEquiv] at this
    exact this.2
  · intro hx_amb₂
    have : (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
        FracIdealsCoprime_subgroup K 𝔪₁ ⊓ p₂.toAmbientSubgroup :=
      ⟨hx_in_I₁, hx_amb₂⟩
    rw [h_isEquiv] at this
    exact this.2

theorem isEquiv_of_dvd_comap (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (hdvd : Modulus.dvd 𝔪 𝔫)
    (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (𝒞_𝔫 : Subgroup (FracIdealsCoprime K 𝔫))
    (h_cong_𝔫 : IsCongruenceSubgroup K 𝔫 𝒞_𝔫)
    (h_eq : 𝒞_𝔫 = Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd) 𝒞) :
    (⟨𝔪, 𝒞, h_cong.contains_ray⟩ : CongruenceSubgroupPair K).IsEquiv
      ⟨𝔫, 𝒞_𝔫, h_cong_𝔫.contains_ray⟩ := by


  show FracIdealsCoprime_subgroup K 𝔪 ⊓
      (𝒞_𝔫.map (FracIdealsCoprime_subgroup K 𝔫).subtype) =
    FracIdealsCoprime_subgroup K 𝔫 ⊓
      (𝒞.map (FracIdealsCoprime_subgroup K 𝔪).subtype)
  ext a
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  ·
    rintro ⟨ha_cop_m, z, hz_in, hz_eq⟩
    constructor
    · rw [← hz_eq]; exact z.2
    ·
      have hz_comap : FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd z ∈ 𝒞 := by
        have : z ∈ Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd) 𝒞 :=
          h_eq ▸ hz_in
        exact Subgroup.mem_comap.mp this
      exact ⟨FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd z, hz_comap, by
        have := FracIdealsCoprime.subtype_inclusion K 𝔪 𝔫 hdvd z
        simp only [Subgroup.coe_subtype] at this hz_eq ⊢
        exact this.symm.trans hz_eq⟩
  ·
    rintro ⟨ha_cop_n, c, hc_in, hc_eq⟩
    refine ⟨?_, ?_⟩
    ·
      rw [← hc_eq]; exact c.2
    ·
      refine ⟨⟨a, ha_cop_n⟩, ?_, rfl⟩

      rw [h_eq]

      have hval : FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd ⟨a, ha_cop_n⟩ = c := by
        apply Subtype.ext
        have h1 := FracIdealsCoprime.subtype_inclusion K 𝔪 𝔫 hdvd (⟨a, ha_cop_n⟩ : FracIdealsCoprime K 𝔫)
        simp only [Subgroup.coe_subtype] at h1 hc_eq
        exact h1.trans hc_eq.symm
      exact Subgroup.mem_comap.mpr (hval ▸ hc_in)




lemma gcd_weight_lt_of_not_dvd {K : Type u} [Field K] [NumberField K]
    {𝔪₁ 𝔪₂ : Modulus K} (h : ¬ 𝔪₁.dvd 𝔪₂) :
    (𝔪₁.gcd 𝔪₂).weight < 𝔪₁.weight := by
  simp only [Modulus.dvd, not_forall, not_le] at h
  obtain ⟨v₀, hv₀⟩ := h
  have hgcd_v₀ : (𝔪₁.gcd 𝔪₂).toFun v₀ < 𝔪₁.toFun v₀ := by
    simp only [Modulus.gcd]
    exact lt_of_le_of_lt (min_le_right _ _) hv₀
  have hgcd_le : ∀ v, (𝔪₁.gcd 𝔪₂).toFun v ≤ 𝔪₁.toFun v := fun v => by
    simp only [Modulus.gcd]; exact min_le_left _ _
  have hv₀_supp : v₀ ∈ 𝔪₁.finite_support.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    omega
  have hsub : (𝔪₁.gcd 𝔪₂).finite_support.toFinset ⊆ 𝔪₁.finite_support.toFinset := by
    intro v hv
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv ⊢
    intro heq
    exact hv (by simp only [Modulus.gcd]; omega)
  unfold Modulus.weight
  calc (𝔪₁.gcd 𝔪₂).finite_support.toFinset.sum (𝔪₁.gcd 𝔪₂).toFun
      ≤ 𝔪₁.finite_support.toFinset.sum (𝔪₁.gcd 𝔪₂).toFun := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ < 𝔪₁.finite_support.toFinset.sum 𝔪₁.toFun := by
        exact Finset.sum_lt_sum (fun v _ => hgcd_le v) ⟨v₀, hv₀_supp, hgcd_v₀⟩





abbrev RayClassCharacter (K : Type u) [Field K] [NumberField K] (𝔪 : Modulus K) : Type u :=
  RayClassGroup K 𝔪 →* ℂˣ

def RayClassGroup.mapOfDvd {K : Type u} [Field K] [NumberField K]
    {𝔪₁ 𝔪₂ : Modulus K} (h : Modulus.dvd 𝔪₁ 𝔪₂) :
    RayClassGroup K 𝔪₂ →* RayClassGroup K 𝔪₁ :=
  QuotientGroup.map (RayGroup K 𝔪₂) (RayGroup K 𝔪₁)
    (FracIdealsCoprime.inclusion K 𝔪₁ 𝔪₂ h)
    (fun x hx => RayGroup.inclusion_le K 𝔪₁ 𝔪₂ h x hx)

def IsInducedBy (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K) (h : Modulus.dvd 𝔪₁ 𝔪₂)
    (χ₁ : RayClassCharacter K 𝔪₁) (χ₂ : RayClassCharacter K 𝔪₂) : Prop :=
  χ₂ = χ₁.comp (RayClassGroup.mapOfDvd h)

def kernelCongruenceSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) : Subgroup (FracIdealsCoprime K 𝔪) :=
  Subgroup.comap (QuotientGroup.mk' (RayGroup K 𝔪)) (MonoidHom.ker χ)

theorem kernelCongruenceSubgroup_isCong (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) :
    IsCongruenceSubgroup K 𝔪 (kernelCongruenceSubgroup K 𝔪 χ) := by
  refine ⟨fun x hx => ?_⟩
  show x ∈ kernelCongruenceSubgroup K 𝔪 χ
  unfold kernelCongruenceSubgroup
  simp only [Subgroup.mem_comap]
  have hq : (QuotientGroup.mk' (RayGroup K 𝔪)) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx
  rw [hq]
  exact (MonoidHom.ker χ).one_mem



def IsRayClassCharacterPrincipal (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) : Prop :=
  χ = 1



noncomputable def PrimeToFracIdealsCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝔭 : Prime' K) (h_coprime : 𝔪 (Place.finite 𝔭) = 0) :
    FracIdealsCoprime K 𝔪 := primeCoprime K 𝔪 𝔭 h_coprime

def primesInCongruenceSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) :
    Set (Prime' K) :=
  {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
    PrimeToFracIdealsCoprime K 𝔪 𝔭 h ∈ 𝒞}

noncomputable def PrimitiveCharsContaining (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) : Type u :=
  (FracIdealsCoprime K 𝔪 ⧸ 𝒞) →* ℂˣ

lemma IsCongruenceSubgroup.finiteIndex {K : Type u} [Field K] [NumberField K]
    {𝔪 : Modulus K} {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) : 𝒞.FiniteIndex := by
  haveI : Finite (FracIdealsCoprime K 𝔪 ⧸ RayGroup K 𝔪) :=
    inferInstanceAs (Finite (RayClassGroup K 𝔪))
  haveI : (RayGroup K 𝔪).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.finiteIndex_of_le h_cong.contains_ray

noncomputable instance instFintypePrimitiveCharsContaining (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    [𝒞.FiniteIndex] :
    Fintype (PrimitiveCharsContaining K 𝔪 𝒞) := by
  unfold PrimitiveCharsContaining
  haveI : Finite (FracIdealsCoprime K 𝔪 ⧸ 𝒞) := Subgroup.finite_quotient_of_finiteIndex

  exact Fintype.ofFinite _

noncomputable def toRayClassCharOfPrimitive (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (χ : PrimitiveCharsContaining K 𝔪 𝒞) : RayClassCharacter K 𝔪 := by
  classical


  by_cases h : RayGroup K 𝔪 ≤ 𝒞
  · exact χ.comp (QuotientGroup.map (RayGroup K 𝔪) 𝒞 (MonoidHom.id _) (fun _ hx => h hx))
  · exact 1


def isPrincipalPrimitive (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (χ : PrimitiveCharsContaining K 𝔪 𝒞) : Prop :=
  IsRayClassCharacterPrincipal K 𝔪 (toRayClassCharOfPrimitive K 𝔪 𝒞 χ)

instance instDecidableIsPrincipalPrimitive (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (χ : PrimitiveCharsContaining K 𝔪 𝒞) :
    Decidable (isPrincipalPrimitive K 𝔪 𝒞 χ) := by
  unfold isPrincipalPrimitive IsRayClassCharacterPrincipal
  exact Classical.dec _



noncomputable def dirichletDensityCoset (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (I : FracIdealsCoprime K 𝔪) : ℚ :=
  (DirichletDensity K {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
    (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
      FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk I}).getD 0

theorem congruenceSubgroup_index_pos (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
    0 < 𝒞.index := by
  haveI : Finite (FracIdealsCoprime K 𝔪 ⧸ RayGroup K 𝔪) :=
    inferInstanceAs (Finite (RayClassGroup K 𝔪))
  haveI : (RayGroup K 𝔪).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : 𝒞.FiniteIndex := Subgroup.finiteIndex_of_le h_cong.contains_ray
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero












theorem summable_rpow_inv_absNorm_prime {K : Type*} [Field K] [NumberField K]
    (S : Set (Prime' K)) (s : ℝ) (hs : 1 < s) :
    Summable (fun (𝔭 : S) => ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) :=
  partialDedekindZeta_dirichletSeries_summable S s hs





theorem ps9_dirichletDensity_mono {K : Type*} [Field K] [NumberField K]
    {S T : Set (Prime' K)} {ρS ρT : ℚ}
    (hST : S ⊆ T)
    (hS : HasDirichletDensity K S ρS)
    (hT : HasDirichletDensity K T ρT) :
    ρS ≤ ρT := by

  suffices h : (ρS : ℝ) ≤ (ρT : ℝ) from mod_cast h

  apply le_of_tendsto_of_tendsto hS hT


  have hIoo : Set.Ioo (1 : ℝ) 2 ∈ nhdsWithin 1 (Set.Ioi 1) :=
    Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)
  filter_upwards [hIoo] with s hs
  have hs_gt : 1 < s := hs.1
  have hs_lt : s < 2 := hs.2

  have hlog_pos : 0 < Real.log (1 / (s - 1)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < s - 1)]
    linarith

  apply div_le_div_of_nonneg_right _ hlog_pos.le
  exact Summable.tsum_le_tsum_of_inj (Set.inclusion hST)
    (Set.inclusion_injective hST)
    (fun c _ => by positivity)
    (fun i => le_refl _)
    (summable_rpow_inv_absNorm_prime S s hs_gt)
    (summable_rpow_inv_absNorm_prime T s hs_gt)



noncomputable def extensionAdmissibleModulus (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Modulus K where
  toFun _ := 0
  finite_support := by simp [Set.finite_empty]
  inf_le_one := fun _ => Nat.zero_le 1
  complex_zero := fun _ _ => rfl

noncomputable def extensionNormSubgroup (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Subgroup (FracIdealsCoprime K (extensionAdmissibleModulus K L)) :=
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq (fun _ => by simp)
  haveI : FiniteDimensional ℚ L := Module.Finite.trans K L
  haveI : NumberField L := NumberField.mk
  NormGroup K L (extensionAdmissibleModulus K L)

theorem extensionNormSubgroup_isCong (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    IsCongruenceSubgroup K (extensionAdmissibleModulus K L)
      (extensionNormSubgroup K L) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq (fun _ => by simp)
  haveI : FiniteDimensional ℚ L := Module.Finite.trans K L
  haveI : NumberField L := NumberField.mk
  exact ⟨rayGroup_le_normGroup K L (extensionAdmissibleModulus K L)⟩


def IsUnramifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
    𝔔.LiesOver 𝔭.asIdeal →
    Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) 𝔔

def IsTamelyRamifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
    𝔔.LiesOver 𝔭.asIdeal →
      ¬ (ringChar (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) ∣
          Ideal.ramificationIdx 𝔭.asIdeal 𝔔)

def IsWildlyRamifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∃ (𝔔 : Ideal (NumberField.RingOfIntegers L)) (_ : 𝔔.IsPrime),
    𝔔.LiesOver 𝔭.asIdeal ∧
      ringChar (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) ∣
        Ideal.ramificationIdx 𝔭.asIdeal 𝔔

def IsTotallyRamifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
    𝔔.LiesOver 𝔭.asIdeal →
      Ideal.inertiaDeg 𝔭.asIdeal 𝔔 = 1

def IsTotallyTamelyRamified (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  IsTotallyRamifiedIn K L 𝔭 ∧ IsTamelyRamifiedIn K L 𝔭

def IsTotallyWildlyRamified (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  IsTotallyRamifiedIn K L 𝔭 ∧
    ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
      𝔔.LiesOver 𝔭.asIdeal →
        ∃ k : ℕ, Ideal.ramificationIdx 𝔭.asIdeal 𝔔 =
          (ringChar (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal)) ^ k






lemma extensionNormSubgroup_equiv_at_modulus (K : Type u) (L : Type u)
    [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔫 : Modulus K) :
    ∃ 𝒟 : Subgroup (FracIdealsCoprime K 𝔫),
      IsCongruenceSubgroup K 𝔫 𝒟 ∧
      CongruenceSubgroupEquiv K (extensionAdmissibleModulus K L) 𝔫
        (extensionNormSubgroup K L) 𝒟 := by


  set 𝔪 := extensionAdmissibleModulus K L
  have h_dvd_m_n : Modulus.dvd 𝔪 𝔫 := fun v => Nat.zero_le _

  set 𝒟 := Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 h_dvd_m_n)
    (extensionNormSubgroup K L)
  refine ⟨𝒟, ?_, ?_⟩


  · constructor
    intro x hx
    show (FracIdealsCoprime.inclusion K 𝔪 𝔫 h_dvd_m_n) x ∈ extensionNormSubgroup K L


    exact (extensionNormSubgroup_isCong K L).contains_ray
      (RayGroup.inclusion_le K 𝔪 𝔫 h_dvd_m_n x hx)


  · refine ⟨𝔫, h_dvd_m_n, fun v => le_refl _, ?_⟩


    show 𝒟 = Subgroup.comap (FracIdealsCoprime.inclusion K 𝔫 𝔫 _) 𝒟
    ext x
    simp only [Subgroup.mem_comap]
    constructor
    · intro hx; convert hx using 1
    · intro hx; convert hx using 1



noncomputable def NormGroup (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Modulus K) : Subgroup (FracIdealsCoprime K 𝔪) :=
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  letI : FiniteDimensional ℚ L := FiniteDimensional.trans ℚ K L
  letI : NumberField L := NumberField.mk

  RayClassField.NormGroup K L 𝔪


noncomputable def choosePrimeOverHOS (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prime' L :=
  ⟨choosePrimeOver K L 𝔭, choosePrimeOver_isPrime K L 𝔭, choosePrimeOver_ne_bot K L 𝔭⟩

lemma choosePrimeOverHOS_lyingUnder (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) :
    lyingUnder K L (choosePrimeOverHOS K L 𝔭) = 𝔭 := by
  ext
  simp only [lyingUnder, IsDedekindDomain.HeightOneSpectrum.under_asIdeal,
    choosePrimeOverHOS, choosePrimeOver_over]

theorem theorem_6_10_norm_prime
    (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔮 : Prime' L) :
    fracIdealNorm K L (primeAsUnitFracIdeal L 𝔮) =
      (primeAsUnitFracIdeal K (lyingUnder K L 𝔮)) ^ (inertiaDegree' K L 𝔮) := by
  exact fracIdealNorm_prime_eq K L 𝔮

lemma primeAbove_coprime_extendModulus
    (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔪 : Modulus K) (𝔭 : Prime' K) (𝔮 : Prime' L)
    (h_over : lyingUnder K L 𝔮 = 𝔭)
    (h_coprime : 𝔪 (Place.finite 𝔭) = 0) :
    (extendModulus K L 𝔪) (Place.finite 𝔮) = 0 := by
  simp only [extendModulus]
  rw [h_over]
  simp only [Nat.mul_eq_zero]
  exact Or.inr h_coprime

theorem splitsCompletely_inertiaDeg_eq_one
    (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Prime' K) (𝔮 : Prime' L)
    (h_split : SplitsCompletely K L 𝔭)
    (h_over : lyingUnder K L 𝔮 = 𝔭) :
    inertiaDegree' K L 𝔮 = 1 := by


  have h_frob_eq_one : FrobeniusAutomorphism K L 𝔭 = 1 := h_split

  let Q₀ := choosePrimeOver K L 𝔭
  have h_isArith : IsArithFrobAt (NumberField.RingOfIntegers K)
      (arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q₀) Q₀ :=
    IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q₀

  rw [FrobeniusAutomorphism] at h_frob_eq_one
  rw [h_frob_eq_one] at h_isArith


  have h_pow : ∀ x : NumberField.RingOfIntegers L ⧸ Q₀,
      x ^ Nat.card (NumberField.RingOfIntegers K ⧸ Ideal.under (NumberField.RingOfIntegers K) Q₀) = x := by
    intro x
    have := h_isArith.restrict_apply x


    have hrestr_id : ∀ y : NumberField.RingOfIntegers L ⧸ Q₀, h_isArith.restrict y = y := by
      intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      show Ideal.Quotient.mk Q₀ ((MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) (1 : L ≃ₐ[K] L)) y) = Ideal.Quotient.mk Q₀ y
      congr 1
    rw [← this, hrestr_id]


  haveI hQ₀_prime : Q₀.IsPrime := choosePrimeOver_isPrime K L 𝔭
  haveI hQ₀_finite : Finite (NumberField.RingOfIntegers L ⧸ Q₀) :=
    choosePrimeOver_finite K L 𝔭
  haveI : Fintype (NumberField.RingOfIntegers L ⧸ Q₀) := Fintype.ofFinite _
  let P₀ := Ideal.under (NumberField.RingOfIntegers K) Q₀
  haveI : Finite (NumberField.RingOfIntegers K ⧸ P₀) :=
    Finite.of_injective _ Ideal.algebraMap_quotient_injective
  haveI : Fintype (NumberField.RingOfIntegers K ⧸ P₀) := Fintype.ofFinite _
  have h_pow_card : ∀ x : NumberField.RingOfIntegers L ⧸ Q₀,
      x ^ Fintype.card (NumberField.RingOfIntegers K ⧸ P₀) = x := by
    intro x
    rw [← Nat.card_eq_fintype_card]
    exact h_pow x

  have hP₀_eq : P₀ = 𝔭.asIdeal := choosePrimeOver_over K L 𝔭

  haveI hQ₀_max : Q₀.IsMaximal :=
    hQ₀_prime.isMaximal (choosePrimeOver_ne_bot K L 𝔭)

  haveI hP₀_max : P₀.IsMaximal := hP₀_eq ▸ (𝔭.isPrime.isMaximal 𝔭.ne_bot)

  letI : Field (NumberField.RingOfIntegers K ⧸ P₀) := Ideal.Quotient.field P₀
  letI : Field (NumberField.RingOfIntegers L ⧸ Q₀) := Ideal.Quotient.field Q₀

  letI : Algebra (NumberField.RingOfIntegers K ⧸ P₀)
      (NumberField.RingOfIntegers L ⧸ Q₀) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq rfl)
  have h_finrank_one : Module.finrank (NumberField.RingOfIntegers K ⧸ P₀)
      (NumberField.RingOfIntegers L ⧸ Q₀) = 1 := by
    have hfrob_eq : FiniteField.frobeniusAlgHom (NumberField.RingOfIntegers K ⧸ P₀)
        (NumberField.RingOfIntegers L ⧸ Q₀) = 1 := by
      apply AlgHom.ext
      intro x
      show x ^ Fintype.card (NumberField.RingOfIntegers K ⧸ P₀) = x
      exact h_pow_card x
    rw [← FiniteField.orderOf_frobeniusAlgHom, hfrob_eq, orderOf_one]

  have h_comap : Ideal.comap (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)) Q₀ = P₀ := rfl
  have h_inertiaDeg_Q₀ : Ideal.inertiaDeg P₀ Q₀ = 1 := by
    unfold Ideal.inertiaDeg
    simp only [h_comap]
    convert h_finrank_one

  unfold inertiaDegree'
  rw [h_over]


  rw [hP₀_eq] at h_inertiaDeg_Q₀
  haveI : 𝔮.asIdeal.IsPrime := 𝔮.isPrime
  haveI : Finite (NumberField.RingOfIntegers L ⧸ 𝔮.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ 𝔮.ne_bot

  haveI : Q₀.LiesOver 𝔭.asIdeal := Ideal.LiesOver.mk hP₀_eq.symm
  have h𝔮_over_asIdeal : 𝔭.asIdeal = Ideal.under (NumberField.RingOfIntegers K) 𝔮.asIdeal := by
    have := IsDedekindDomain.HeightOneSpectrum.under_asIdeal (NumberField.RingOfIntegers K) 𝔮
    rw [← this]
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h_over.symm
  haveI : 𝔮.asIdeal.LiesOver 𝔭.asIdeal := Ideal.LiesOver.mk h𝔮_over_asIdeal
  rw [← h_inertiaDeg_Q₀]
  exact (Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔭.asIdeal Q₀ 𝔮.asIdeal (L ≃ₐ[K] L)).symm





structure IsHilbertClassField (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsAbelianExtension K L] : Prop where
  finiteDimensional : FiniteDimensional K L
  everywhere_unramified : ∀ 𝔭 : Prime' K, IsUnramifiedIn K L 𝔭
  maximal :
    ∀ (M : Type u) [Field M] [NumberField M] [Algebra K M] [IsAbelianExtension K M]
      [FiniteDimensional K M],
      (∀ 𝔭 : Prime' K, IsUnramifiedIn K M 𝔭) → Nonempty (M →ₐ[K] L)



end GlobalCFT

open Ideles

structure GlobalArtinMap (K : Type*) [Field K] [NumberField K] where
  I : Type*
  [instPreorder : Preorder I]
  GalLK : I → Type*
  [instFintype : ∀ i, Fintype (GalLK i)]
  [instCommGroup : ∀ i, CommGroup (GalLK i)]
  restrictMap : ∀ {i j : I}, i ≤ j → GalLK j →* GalLK i
  artinMap : ∀ i, IdeleGroup K →* GalLK i
  artinMap_compat : ∀ {i j : I} (h : i ≤ j) (a : IdeleGroup K),
    restrictMap h (artinMap j a) = artinMap i a
  GalAb : Type*
  [galAb_group : CommGroup GalAb]
  [galAb_topologicalSpace : TopologicalSpace GalAb]
  [galAb_topologicalGroup : IsTopologicalGroup GalAb]
  [galAb_compactSpace : CompactSpace GalAb]
  artinHom : IdeleGroup K →* GalAb
  artinHom_continuous : Continuous artinHom
  proj : ∀ i, GalAb →* GalLK i
  artinMap_eq_proj : ∀ i (a : IdeleGroup K), artinMap i a = proj i (artinHom a)
  artinMap_surjective : ∀ i, Function.Surjective (artinMap i)
  proj_jointly_injective : ∀ g : GalAb, (∀ i, proj i g = 1) → g = 1
  proj_compat : ∀ {i j : I} (h : i ≤ j) (g : GalAb),
    restrictMap h (proj j g) = proj i g
  principalInKer : principalIdeles K ≤ MonoidHom.ker artinHom
  normSubgroup : ∀ i, Subgroup (IdeleClassGroup K)
  normSubgroup_normal : ∀ i, (normSubgroup i).Normal
  artinMapCK_surjective : ∀ i, Function.Surjective
    ((proj i).comp (QuotientGroup.lift (principalIdeles K) artinHom principalInKer))
  ker_eq_normSubgroup : ∀ i, MonoidHom.ker
    ((proj i).comp (QuotientGroup.lift (principalIdeles K) artinHom principalInKer)) =
    normSubgroup i
attribute [instance] GlobalArtinMap.instPreorder
  GlobalArtinMap.instFintype
  GlobalArtinMap.instCommGroup
  GlobalArtinMap.galAb_group
  GlobalArtinMap.galAb_topologicalSpace
  GlobalArtinMap.galAb_topologicalGroup
  GlobalArtinMap.galAb_compactSpace

namespace GlobalArtinMap
end GlobalArtinMap

theorem proposition_28_3 {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K)
    (θ' : IdeleGroup K →* θ.GalAb)
    (hcompat : ∀ (i : θ.I) (a : IdeleGroup K), θ.proj i (θ' a) = θ.artinMap i a) :
    ∀ (a : IdeleGroup K), θ' a = θ.artinHom a := by
  intro a
  have h : ∀ i : θ.I, θ.proj i (θ' a * (θ.artinHom a)⁻¹) = 1 := by
    intro i
    rw [map_mul, map_inv]
    rw [hcompat i a, θ.artinMap_eq_proj i a]
    exact mul_inv_cancel _
  have := θ.proj_jointly_injective (θ' a * (θ.artinHom a)⁻¹) h
  rwa [mul_inv_eq_one] at this

theorem theorem_28_4_principal_in_ker {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) :
    principalIdeles K ≤ MonoidHom.ker θ.artinHom :=
  θ.principalInKer

noncomputable def GlobalArtinMap.artinHomCK {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) :
    IdeleClassGroup K →* θ.GalAb :=
  QuotientGroup.lift (principalIdeles K) θ.artinHom (theorem_28_4_principal_in_ker θ)

theorem GlobalArtinMap.artinHomCK_comp {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (a : IdeleGroup K) :
    θ.artinHomCK (QuotientGroup.mk a) = θ.artinHom a := by
  simp only [artinHomCK, QuotientGroup.lift_mk']

noncomputable def GlobalArtinMap.normSubgroupCK {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (i : θ.I) :
    Subgroup (IdeleClassGroup K) :=
  θ.normSubgroup i

theorem GlobalArtinMap.normSubgroupCK_normal {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (i : θ.I) :
    (θ.normSubgroupCK i).Normal :=
  θ.normSubgroup_normal i

attribute [instance] GlobalArtinMap.normSubgroupCK_normal

noncomputable def GlobalArtinMap.artinMapCK {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (i : θ.I) :
    IdeleClassGroup K →* θ.GalLK i :=
  (θ.proj i).comp θ.artinHomCK

theorem theorem_28_4_ker_eq_norm {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (i : θ.I) :
    MonoidHom.ker (θ.artinMapCK i) = θ.normSubgroupCK i :=
  θ.ker_eq_normSubgroup i

theorem theorem_28_4_iso {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (i : θ.I) :
    Nonempty (IdeleClassGroup K ⧸ θ.normSubgroupCK i ≃* θ.GalLK i) :=
  ⟨QuotientGroup.liftEquiv (θ.normSubgroupCK i)
    (θ.artinMapCK_surjective i) (θ.ker_eq_normSubgroup i).symm⟩


section Chebotarev

universe w

open NumberField RayClassField GlobalCFT

def IsConjugationStable {G : Type*} [Group G] (C : Set G) : Prop :=
  ∀ g : G, ∀ c ∈ C, g * c * g⁻¹ ∈ C

noncomputable def FrobeniusConjClass (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (𝔭 : Prime' K) : Set (L ≃ₐ[K] L) :=
  {σ : L ≃ₐ[K] L | ∃ (𝔔 : Ideal (RingOfIntegers L)),
    𝔔.IsPrime ∧ 𝔔.LiesOver 𝔭.asIdeal ∧
    IsArithFrobAt (RingOfIntegers K) σ 𝔔}

theorem FrobeniusConjClass.nonempty (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (𝔭 : Prime' K) (_h_unram : GlobalCFT.IsUnramifiedIn K L 𝔭) :
    (FrobeniusConjClass K L 𝔭).Nonempty := by
  have h𝔭 := 𝔭.isPrime
  have h_inj := RingOfIntegers.algebraMap.injective K L
  obtain ⟨𝔔, _, h𝔔_prime, h𝔔_comap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := RingOfIntegers L) 𝔭.asIdeal ⊥
      (by rw [Ideal.comap_bot_of_injective _ h_inj]; exact bot_le)
  have h𝔔_ne_bot : 𝔔 ≠ ⊥ := by
    intro h
    rw [h, Ideal.comap_bot_of_injective _ h_inj] at h𝔔_comap
    exact 𝔭.ne_bot h𝔔_comap.symm
  haveI : 𝔔.IsMaximal := Ideal.IsPrime.isMaximal h𝔔_prime h𝔔_ne_bot
  haveI : 𝔔.IsPrime := h𝔔_prime
  haveI : Finite (RingOfIntegers L ⧸ 𝔔) := inferInstance
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (RingOfIntegers K) (L ≃ₐ[K] L) 𝔔
  exact ⟨σ, 𝔔, h𝔔_prime, ⟨h𝔔_comap.symm⟩, hσ⟩

def primesWithFrobInSet (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (C : Set (L ≃ₐ[K] L)) : Set (Prime' K) :=
  {𝔭 : Prime' K | GlobalCFT.IsUnramifiedIn K L 𝔭 ∧ FrobeniusConjClass K L 𝔭 ⊆ C}

theorem rayGroup_isCongruenceSubgroup (K : Type w) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    IsCongruenceSubgroup K 𝔪 (RayGroup K 𝔪) :=
  ⟨le_refl _⟩

theorem rayGroup_index_eq_natCard (K : Type w) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    (RayGroup K 𝔪).index = Nat.card (RayClassGroup K 𝔪) := by
  rw [Subgroup.index_eq_card]
  rfl



noncomputable def liftToGalLE {K L : Type*} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) :
    L ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers σ)] L :=
  IntermediateField.fixingSubgroupEquiv
    (IntermediateField.fixedField (Subgroup.zpowers σ))
    ⟨σ, by rw [IntermediateField.fixingSubgroup_fixedField]; exact Subgroup.mem_zpowers σ⟩






set_option maxHeartbeats 800000 in
theorem dirichletDensity_disjoint_union (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (A B : Set (L ≃ₐ[K] L))
    (hA : IsConjugationStable A) (hB : IsConjugationStable B)
    (h_disj : Disjoint A B)
    (dA dB : ℚ)
    (hdA : HasDirichletDensity K (primesWithFrobInSet K L A) dA)
    (hdB : HasDirichletDensity K (primesWithFrobInSet K L B) dB) :
    HasDirichletDensity K (primesWithFrobInSet K L (A ∪ B)) (dA + dB) := by


  have h_set : primesWithFrobInSet K L (A ∪ B) =
      primesWithFrobInSet K L A ∪ primesWithFrobInSet K L B := by
    ext 𝔭
    simp only [primesWithFrobInSet, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨h_unram, h_sub⟩
      obtain ⟨σ, hσ⟩ := FrobeniusConjClass.nonempty K L 𝔭 h_unram

      have frob_conj : ∀ τ, τ ∈ FrobeniusConjClass K L 𝔭 →
          ∃ g : L ≃ₐ[K] L, τ = g * σ * g⁻¹ := by
        intro τ hτ
        obtain ⟨𝔔₁, h𝔔₁_prime, h𝔔₁_over, h𝔔₁_frob⟩ := hσ
        obtain ⟨𝔔₂, h𝔔₂_prime, h𝔔₂_over, h𝔔₂_frob⟩ := hτ
        haveI : 𝔔₁.IsPrime := h𝔔₁_prime
        haveI : 𝔔₂.IsPrime := h𝔔₂_prime

        have h_under_eq : 𝔔₁.under (RingOfIntegers K) = 𝔔₂.under (RingOfIntegers K) := by
          rw [← h𝔔₁_over.over, ← h𝔔₂_over.over]

        obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
          (RingOfIntegers K) (RingOfIntegers L) (L ≃ₐ[K] L) 𝔔₁ 𝔔₂ h_under_eq

        have h_conj_frob : IsArithFrobAt (RingOfIntegers K) (g * σ * g⁻¹) 𝔔₂ :=
          hg ▸ h𝔔₁_frob.conj g

        haveI : Algebra.IsUnramifiedAt (RingOfIntegers K) 𝔔₂ := h_unram 𝔔₂ h𝔔₂_over
        have hQ : 𝔔₂.primeCompl ≤ nonZeroDivisors (RingOfIntegers L) :=
          Ideal.primeCompl_le_nonZeroDivisors 𝔔₂
        have h_alg_eq := h𝔔₂_frob.eq_of_isUnramifiedAt h_conj_frob hQ
        haveI : FaithfulSMul (L ≃ₐ[K] L) (RingOfIntegers L) := by
          constructor
          intro σ' τ' h'
          have hL : ∀ (a : RingOfIntegers L), σ' (a : L) = τ' (a : L) :=
            fun a => congr_arg Subtype.val (h' a)
          have h_ring : σ'.toRingHom.comp (algebraMap (RingOfIntegers L) L) =
              τ'.toRingHom.comp (algebraMap (RingOfIntegers L) L) :=
            RingHom.ext fun a => hL a
          exact AlgEquiv.ext fun x => RingHom.congr_fun
            (IsLocalization.ringHom_ext (nonZeroDivisors (RingOfIntegers L)) h_ring) x
        exact ⟨g, MulSemiringAction.toAlgHom_injective
          (RingOfIntegers K) (RingOfIntegers L) h_alg_eq⟩
      cases h_sub hσ with
      | inl hσ_A =>
        left; exact ⟨h_unram, fun τ hτ => by
          obtain ⟨g, hg⟩ := frob_conj τ hτ; rw [hg]; exact hA g σ hσ_A⟩
      | inr hσ_B =>
        right; exact ⟨h_unram, fun τ hτ => by
          obtain ⟨g, hg⟩ := frob_conj τ hτ; rw [hg]; exact hB g σ hσ_B⟩
    · rintro (⟨h_unram, h_sub_A⟩ | ⟨h_unram, h_sub_B⟩)
      · exact ⟨h_unram, h_sub_A.trans Set.subset_union_left⟩
      · exact ⟨h_unram, h_sub_B.trans Set.subset_union_right⟩

  have h_disj_primes : Disjoint (primesWithFrobInSet K L A) (primesWithFrobInSet K L B) := by
    rw [Set.disjoint_iff]
    intro 𝔭 ⟨h𝔭_A, h𝔭_B⟩
    obtain ⟨h_unram, h_sub_A⟩ := h𝔭_A
    obtain ⟨_, h_sub_B⟩ := h𝔭_B
    obtain ⟨σ, hσ⟩ := FrobeniusConjClass.nonempty K L 𝔭 h_unram
    exact Set.disjoint_iff.mp h_disj ⟨h_sub_A hσ, h_sub_B hσ⟩

  rw [h_set]
  show HasDirichletDensity K
    (primesWithFrobInSet K L A ∪ primesWithFrobInSet K L B) (dA + dB)
  unfold HasDirichletDensity
  rw [show ((dA + dB : ℚ) : ℝ) = (↑dA : ℝ) + (↑dB : ℝ) from by push_cast; ring]


  have h_ev_eq : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1),
      (fun s => (∑' (𝔭 : ↑(primesWithFrobInSet K L A)),
          ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) /
          Real.log (1 / (s - 1)) +
        (∑' (𝔭 : ↑(primesWithFrobInSet K L B)),
          ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) /
          Real.log (1 / (s - 1))) s =
      (fun s => (∑' (𝔭 : ↑(primesWithFrobInSet K L A ∪ primesWithFrobInSet K L B)),
          ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) /
          Real.log (1 / (s - 1))) s := by
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro s (hs : 1 < s)
    dsimp only
    rw [← add_div]
    congr 1
    let f : Prime' K → ℝ := fun 𝔭 => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
    have hsumA : Summable (f ∘ Subtype.val (p := (· ∈ primesWithFrobInSet K L A))) :=
      summable_rpow_inv_absNorm_prime (primesWithFrobInSet K L A) s hs
    have hsumB : Summable (f ∘ Subtype.val (p := (· ∈ primesWithFrobInSet K L B))) :=
      summable_rpow_inv_absNorm_prime (primesWithFrobInSet K L B) s hs
    exact (Summable.tsum_union_disjoint h_disj_primes hsumA hsumB).symm
  exact (Filter.Tendsto.add hdA hdB).congr' h_ev_eq
theorem primesWithFrobInSet_empty_hasDensity_zero (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    HasDirichletDensity K (primesWithFrobInSet K L ∅) 0 := by

  have h_empty : primesWithFrobInSet K L ∅ = ∅ := by
    ext 𝔭
    simp only [primesWithFrobInSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h_unram h_sub
    exact (FrobeniusConjClass.nonempty K L 𝔭 h_unram).ne_empty (Set.subset_empty_iff.mp h_sub)

  unfold HasDirichletDensity

  have h_tsum : ∀ s : ℝ, ∑' (𝔭 : ↥(primesWithFrobInSet K L ∅)),
      ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s)) = 0 := by
    intro s
    rw [h_empty]
    exact tsum_empty
  simp_rw [h_tsum, zero_div]
  simp only [Rat.cast_zero]
  exact tendsto_const_nhds

lemma conjClass_subset_of_mem_conjStable {G : Type*} [Group G]
    (C : Set G) (hC : IsConjugationStable C) (σ : G) (hσ : σ ∈ C) :
    (ConjClasses.mk σ).carrier ⊆ C := by
  intro τ hτ
  rw [ConjClasses.mem_carrier_iff_mk_eq] at hτ
  have hconj : IsConj τ σ := ConjClasses.mk_eq_mk_iff_isConj.mp hτ
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj

  have h1 : τ = g⁻¹ * σ * (g⁻¹)⁻¹ := by
    calc τ = g⁻¹ * (g * τ * g⁻¹) * (g⁻¹)⁻¹ := by group
    _ = g⁻¹ * σ * (g⁻¹)⁻¹ := by rw [hg]
  rw [h1]
  exact hC g⁻¹ σ hσ

lemma conjStable_sdiff {G : Type*} [Group G]
    (C : Set G) (hC : IsConjugationStable C) (σ : G) :
    IsConjugationStable (C \ (ConjClasses.mk σ).carrier) := by
  intro g c ⟨hcC, hcCC⟩
  refine ⟨hC g c hcC, ?_⟩
  intro hmem
  apply hcCC
  rw [ConjClasses.mem_carrier_iff_mk_eq] at hmem ⊢
  rw [← hmem]
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g, rfl⟩)



end Chebotarev

section Functoriality

variable {K : Type*} [Field K] [NumberField K]
  {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

open Ideles






end Functoriality

section ArtinMapGaloisCorrespondence

open Ideles

variable {K : Type*} [Field K] [NumberField K]

theorem normSubgroup_finiteIndex (θ : GlobalArtinMap K) (i : θ.I) :
    (θ.normSubgroupCK i).FiniteIndex := by

  have hker : MonoidHom.ker (θ.artinMapCK i) = θ.normSubgroupCK i :=
    theorem_28_4_ker_eq_norm θ i
  rw [← hker]

  exact Subgroup.finiteIndex_ker (θ.artinMapCK i)


theorem artinMap_quotient_iso (θ : GlobalArtinMap K) (i : θ.I) :
    Nonempty (IdeleClassGroup K ⧸ θ.normSubgroupCK i ≃* θ.GalLK i) :=
  theorem_28_4_iso θ i


end ArtinMapGaloisCorrespondence

end
