/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Prop226

noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

lemma Modulus.dvd_trans' {𝔪₁ 𝔪₂ 𝔪₃ : Modulus K}
    (h₁₂ : 𝔪₁.dvd 𝔪₂) (h₂₃ : 𝔪₂.dvd 𝔪₃) : 𝔪₁.dvd 𝔪₃ :=
  fun v => le_trans (h₁₂ v) (h₂₃ v)

lemma Modulus.dvd_refl (𝔪 : Modulus K) : 𝔪.dvd 𝔪 :=
  fun _ => le_refl _

lemma Modulus.dvd_antisymm' {𝔪₁ 𝔪₂ : Modulus K} (h₁ : 𝔪₁.dvd 𝔪₂) (h₂ : 𝔪₂.dvd 𝔪₁) :
    𝔪₁ = 𝔪₂ := by
  have : ∀ v, 𝔪₁ v = 𝔪₂ v := fun v => le_antisymm (h₁ v) (h₂ v)
  cases 𝔪₁; cases 𝔪₂
  congr 1
  funext v
  exact this v

lemma CongruenceSubgroupPair.isEquiv_refl (p : CongruenceSubgroupPair K) :
    p.IsEquiv p := rfl

lemma CongruenceSubgroupPair.IsEquiv.symm' {p₁ p₂ : CongruenceSubgroupPair K}
    (h : p₁.IsEquiv p₂) : p₂.IsEquiv p₁ :=
  h.symm

lemma CongruenceSubgroupPair.IsEquiv.trans_of_dvd {K : Type u} [Field K] [NumberField K]
    {p₁ p₂ p₃ : CongruenceSubgroupPair K}
    (h₁₂ : p₁.IsEquiv p₂) (h₂₃ : p₂.IsEquiv p₃)
    (hdvd₁ : p₂.modulus.dvd p₁.modulus)
    (hdvd₃ : p₂.modulus.dvd p₃.modulus) : p₁.IsEquiv p₃ := by
  have hA₁_le_A₂ : FracIdealsCoprime_subgroup K p₁.modulus ≤
      FracIdealsCoprime_subgroup K p₂.modulus :=
    FracIdealsCoprime_subgroup_mono hdvd₁
  have hA₃_le_A₂ : FracIdealsCoprime_subgroup K p₃.modulus ≤
      FracIdealsCoprime_subgroup K p₂.modulus :=
    FracIdealsCoprime_subgroup_mono hdvd₃
  show FracIdealsCoprime_subgroup K p₁.modulus ⊓ p₃.toAmbientSubgroup =
       FracIdealsCoprime_subgroup K p₃.modulus ⊓ p₁.toAmbientSubgroup
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · intro ⟨hxA₁, hxB₃⟩
    have hxA₃ := p₃.toAmbientSubgroup_le hxB₃
    have hxA₂ := hA₁_le_A₂ hxA₁
    have hxB₂ := (Subgroup.mem_inf.mp (h₂₃ ▸ Subgroup.mem_inf.mpr ⟨hxA₂, hxB₃⟩)).2
    have hxB₁ := (Subgroup.mem_inf.mp (h₁₂ ▸ Subgroup.mem_inf.mpr ⟨hxA₁, hxB₂⟩)).2
    exact ⟨hxA₃, hxB₁⟩
  · intro ⟨hxA₃, hxB₁⟩
    have hxA₁ := p₁.toAmbientSubgroup_le hxB₁
    have hxA₂ := hA₃_le_A₂ hxA₃
    have hxB₂ := (Subgroup.mem_inf.mp (h₁₂.symm ▸ Subgroup.mem_inf.mpr ⟨hxA₂, hxB₁⟩)).2
    have hxB₃ := (Subgroup.mem_inf.mp (h₂₃.symm ▸ Subgroup.mem_inf.mpr ⟨hxA₃, hxB₂⟩)).2
    exact ⟨hxA₁, hxB₃⟩

lemma isEquiv_chain {K : Type u} [Field K] [NumberField K]
    {p₁ p₂ p₃ : CongruenceSubgroupPair K}
    (h₁₂ : p₁.IsEquiv p₂) (h₂₃ : p₂.IsEquiv p₃)
    (hdvd₁₂ : p₂.modulus.dvd p₁.modulus)
    (hdvd₂₃ : p₃.modulus.dvd p₂.modulus) : p₁.IsEquiv p₃ := by
  have hA₁_le_A₂ : FracIdealsCoprime_subgroup K p₁.modulus ≤
      FracIdealsCoprime_subgroup K p₂.modulus :=
    FracIdealsCoprime_subgroup_mono hdvd₁₂
  have _hA₂_le_A₃ : FracIdealsCoprime_subgroup K p₂.modulus ≤
      FracIdealsCoprime_subgroup K p₃.modulus :=
    FracIdealsCoprime_subgroup_mono hdvd₂₃
  show FracIdealsCoprime_subgroup K p₁.modulus ⊓ p₃.toAmbientSubgroup =
       FracIdealsCoprime_subgroup K p₃.modulus ⊓ p₁.toAmbientSubgroup
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · intro ⟨hxA₁, hxB₃⟩
    have hxA₂ := hA₁_le_A₂ hxA₁
    have hxB₂ := (Subgroup.mem_inf.mp (h₂₃ ▸ Subgroup.mem_inf.mpr ⟨hxA₂, hxB₃⟩)).2
    have hxB₁ := (Subgroup.mem_inf.mp (h₁₂ ▸ Subgroup.mem_inf.mpr ⟨hxA₁, hxB₂⟩)).2
    exact ⟨p₃.toAmbientSubgroup_le hxB₃, hxB₁⟩
  · intro ⟨hxA₃, hxB₁⟩
    have hxA₁ := p₁.toAmbientSubgroup_le hxB₁
    have hxA₂ := hA₁_le_A₂ hxA₁
    have hxB₂ := (Subgroup.mem_inf.mp (h₁₂.symm ▸ Subgroup.mem_inf.mpr ⟨hxA₂, hxB₁⟩)).2
    have hxB₃ := (Subgroup.mem_inf.mp (h₂₃.symm ▸ Subgroup.mem_inf.mpr ⟨hxA₃, hxB₂⟩)).2
    exact ⟨hxA₁, hxB₃⟩

lemma IsRayGenerator_of_dvd
    (𝔪₁ 𝔪₂ : Modulus K) (h : 𝔪₁.dvd 𝔪₂)
    (I : FracIdealsCoprime K 𝔪₂) (hI : IsRayGenerator 𝔪₂ I) :
    IsRayGenerator 𝔪₁
      (Subgroup.inclusion (FracIdealsCoprime_subgroup_mono h) I) := by
  obtain ⟨α, hprinc, hcong, hsign⟩ := hI
  refine ⟨α, ?_, ?_, ?_⟩
  · simp only [Subgroup.coe_inclusion]
    exact hprinc
  · intro v hv
    have hv_n : 𝔪₂ (Place.finite v) ≠ 0 := by
      intro h0; exact hv (Nat.eq_zero_of_le_zero (h0 ▸ h (Place.finite v)))
    have hle : (𝔪₁ (Place.finite v) : ℤ) ≤ (𝔪₂ (Place.finite v) : ℤ) :=
      Int.ofNat_le.mpr (h (Place.finite v))
    calc v.valuation K ((α : K) - 1)
        ≤ ↑(Multiplicative.ofAdd (-(𝔪₂ (Place.finite v) : ℤ))) := hcong v hv_n
      _ ≤ ↑(Multiplicative.ofAdd (-(𝔪₁ (Place.finite v) : ℤ))) := by
          simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le]
          linarith
  · intro w hw
    exact hsign w (fun h0 => hw (Nat.eq_zero_of_le_zero (h0 ▸ h (Place.infinite w))))

lemma RayGroup_inclusion_le
    (𝔪₁ 𝔪₂ : Modulus K) (h : 𝔪₁.dvd 𝔪₂) :
    ∀ x : FracIdealsCoprime K 𝔪₂,
      x ∈ RayGroup K 𝔪₂ →
      (Subgroup.inclusion (FracIdealsCoprime_subgroup_mono h)) x ∈ RayGroup K 𝔪₁ := by
  intro x hx


  let f : FracIdealsCoprime K 𝔪₂ →* FracIdealsCoprime K 𝔪₁ :=
    Subgroup.inclusion (FracIdealsCoprime_subgroup_mono h)
  suffices hsuff : Subgroup.map f (RayGroup K 𝔪₂) ≤ RayGroup K 𝔪₁ from
    hsuff ⟨x, hx, rfl⟩

  have hrw : Subgroup.map f (RayGroup K 𝔪₂) =
      Subgroup.closure (f '' {I | IsRayGenerator 𝔪₂ I}) :=
    MonoidHom.map_closure f {I | IsRayGenerator 𝔪₂ I}
  rw [hrw]
  apply Subgroup.closure_mono
  rintro _ ⟨I, hI, rfl⟩
  exact IsRayGenerator_of_dvd 𝔪₁ 𝔪₂ h I hI

lemma RayGroup_toAmbientSubgroup_antitone (K : Type u) [Field K] [NumberField K]
    {𝔪₁ 𝔪₂ : Modulus K} (h : 𝔪₁.dvd 𝔪₂) :
    RayGroup.toAmbientSubgroup K 𝔪₂ ≤ RayGroup.toAmbientSubgroup K 𝔪₁ := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  let y₁ := Subgroup.inclusion (FracIdealsCoprime_subgroup_mono h) y
  have hy₁ : y₁ ∈ RayGroup K 𝔪₁ := RayGroup_inclusion_le 𝔪₁ 𝔪₂ h y hy

  apply Subgroup.mem_map.mpr
  exact ⟨y₁, hy₁, by simp only [Subgroup.subtype_apply]; rfl⟩



noncomputable def Modulus.weight (𝔪 : Modulus K) : ℕ :=
  𝔪.finite_support.toFinset.sum 𝔪.toFun

lemma Modulus.gcd_weight_lt_of_not_dvd {𝔪₁ 𝔪₂ : Modulus K}
    (h : ¬ 𝔪₁.dvd 𝔪₂) : (𝔪₁.gcd 𝔪₂).weight < 𝔪₁.weight := by
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


theorem corollary_22_7_modulus_unique (p p₀ p₀' : CongruenceSubgroupPair K)
    (hp₀ : p.IsEquiv p₀)
    (hp₀_min : ∀ q, p.IsEquiv q → p₀.modulus.dvd q.modulus)
    (hp₀' : p.IsEquiv p₀')
    (hp₀'_min : ∀ q, p.IsEquiv q → p₀'.modulus.dvd q.modulus) :
    p₀.modulus = p₀'.modulus :=
  Modulus.dvd_antisymm' (hp₀_min p₀' hp₀') (hp₀'_min p₀ hp₀)


end RayClassField
