/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace PicardGroup

section PicardGroupDef


variable (Div : Type*) [AddCommGroup Div]
variable (PrincDiv : AddSubgroup Div)

abbrev PicGrp := Div ⧸ PrincDiv

def toPic : Div →+ PicGrp Div PrincDiv :=
  QuotientAddGroup.mk' PrincDiv

def LinearlyEquivalent (D₁ D₂ : Div) : Prop :=
  D₁ - D₂ ∈ PrincDiv


end PicardGroupDef

section DegreeMap

variable {Div : Type*} [AddCommGroup Div]
variable {PrincDiv : AddSubgroup Div}

variable (deg : Div →+ ℤ)

variable (hdeg : PrincDiv ≤ deg.ker)

def degPic : PicGrp Div PrincDiv →+ ℤ :=
  QuotientAddGroup.lift PrincDiv deg hdeg

theorem degPic_toPic (D : Div) :
    degPic deg hdeg (toPic Div PrincDiv D) = deg D := by
  simp [degPic, toPic, QuotientAddGroup.mk'_apply]

def Pic0 : AddSubgroup (PicGrp Div PrincDiv) :=
  (degPic deg hdeg).ker

theorem mem_Pic0_iff (x : PicGrp Div PrincDiv) :
    x ∈ Pic0 deg hdeg ↔ degPic deg hdeg x = 0 := by
  simp [Pic0, AddMonoidHom.mem_ker]

end DegreeMap

end PicardGroup


namespace CanonicalDivisors


variable {F : Type*} [Field F]
variable {Div : Type*} [AddCommGroup Div]
variable {Ω : Type*} [Zero Ω]
variable {Place : Type*}


variable (divF : F → Div) (divΩ : Ω → Div) (smulΩ : F → Ω → Ω)


variable (ordP : Place → Div → ℤ)


variable (omegaD : Ω → Div → Prop)

def IsMaximalDivisorFor [PartialOrder Div] (ω : Ω) (D : Div) : Prop :=
  omegaD ω D ∧ ∀ D' : Div, omegaD ω D' → D' ≤ D

omit [AddCommGroup Div] in
theorem exists_maximal_divisor_for_nonzero_differential [SemilatticeSup Div]
    (omegaD : Ω → Div → Prop)
    (ω : Ω) (_hω : ω ≠ 0)

    (hex : ∃ D, omegaD ω D)

    (hfin : Set.Finite {D | omegaD ω D})


    (hsup : ∀ D₁ D₂, omegaD ω D₁ → omegaD ω D₂ → omegaD ω (D₁ ⊔ D₂)) :
    ∃ D, omegaD ω D ∧ ∀ D' : Div, omegaD ω D' → D' ≤ D := by


  obtain ⟨D₀, hD₀⟩ := hex
  obtain ⟨m, hm⟩ := hfin.exists_maximal ⟨D₀, hD₀⟩
  refine ⟨m, hm.prop, fun D' hD' => ?_⟩


  exact le_trans le_sup_right (hm.le_of_ge (hsup m D' hm.prop hD') le_sup_left)

omit [AddCommGroup Div] in

structure IsDivOmegaMaximal [PartialOrder Div] (ω : Ω) : Prop where
  mem : omegaD ω (divΩ ω)
  le_divΩ : ∀ D : Div, omegaD ω D → D ≤ divΩ ω

omit [AddCommGroup Div] [Zero Ω] in

def div_differential (ω : Ω) : Div := divΩ ω

def IsCanonical (D : Div) : Prop :=
  ∃ ω : Ω, ω ≠ 0 ∧ D = divΩ ω

def ordOmega (P : Place) (ω : Ω) : ℤ := ordP P (divΩ ω)

section APILemmas

variable {Div : Type*} {Ω : Type*} {Place : Type*}
variable {divΩ : Ω → Div} {ordP : Place → Div → ℤ}


end APILemmas

theorem div_smul_eq [PartialOrder Div]
    [CovariantClass Div Div (· + ·) (· ≤ ·)]
    (f : F) (hf : f ≠ 0) (ω : Ω) (_hω : ω ≠ 0)

    (hdivΩ_max : ∀ (ω' : Ω), ω' ≠ 0 → IsDivOmegaMaximal divΩ omegaD ω')


    (omegaD_smul : ∀ (g : F), g ≠ 0 → ∀ (ω' : Ω) (D : Div),
      omegaD ω' D → omegaD (smulΩ g ω') (divF g + D))


    (smul_ne_zero : ∀ (g : F) (ω' : Ω), g ≠ 0 → ω' ≠ 0 → smulΩ g ω' ≠ 0)

    (divF_inv : ∀ (g : F), g ≠ 0 → divF g⁻¹ = -divF g)

    (smul_inv_cancel : ∀ (g : F) (ω' : Ω), g ≠ 0 → smulΩ g⁻¹ (smulΩ g ω') = ω') :
    divΩ (smulΩ f ω) = divF f + divΩ ω := by
  have hfω_ne : smulΩ f ω ≠ 0 := smul_ne_zero f ω hf _hω
  have hmax_ω := hdivΩ_max ω _hω
  have hmax_fω := hdivΩ_max (smulΩ f ω) hfω_ne
  apply le_antisymm
  ·

    have h1 := hmax_fω.mem

    have h2 := omegaD_smul f⁻¹ (inv_ne_zero hf) (smulΩ f ω) (divΩ (smulΩ f ω)) h1
    rw [smul_inv_cancel f ω hf] at h2

    have h3 := hmax_ω.le_divΩ _ h2
    rw [divF_inv f hf] at h3


    have h4 : (divF f) + (-divF f + divΩ (smulΩ f ω)) ≤ (divF f) + divΩ ω :=
      CovariantClass.elim (divF f) h3
    rwa [← add_assoc, add_neg_cancel, zero_add] at h4
  ·

    exact hmax_fω.le_divΩ _ (omegaD_smul f hf ω (divΩ ω) hmax_ω.mem)

def LinearlyEquivalent (D₁ D₂ : Div) : Prop :=
  ∃ f : F, f ≠ 0 ∧ D₂ = D₁ + divF f

theorem canonical_linearlyEquivalent

    (omega_one_dim : ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 →
      ∃ f : F, f ≠ 0 ∧ ω₂ = smulΩ f ω₁)

    (div_smul_eq : ∀ (f : F) (ω : Ω), f ≠ 0 → ω ≠ 0 →
      divΩ (smulΩ f ω) = divF f + divΩ ω)
    {D₁ D₂ : Div}
    (h₁ : IsCanonical divΩ D₁)
    (h₂ : IsCanonical divΩ D₂) :
    LinearlyEquivalent divF D₁ D₂ := by
  obtain ⟨ω₁, hω₁_ne, rfl⟩ := h₁
  obtain ⟨ω₂, hω₂_ne, rfl⟩ := h₂
  obtain ⟨f, hf_ne, hf_eq⟩ := omega_one_dim ω₁ ω₂ hω₁_ne hω₂_ne
  exact ⟨f, hf_ne, by rw [hf_eq, div_smul_eq f ω₁ hf_ne hω₁_ne, add_comm]⟩

theorem isCanonical_of_linearlyEquivalent

    (div_smul_eq : ∀ (f : F) (ω : Ω), f ≠ 0 → ω ≠ 0 →
      divΩ (smulΩ f ω) = divF f + divΩ ω)


    (smul_ne_zero : ∀ (f : F) (ω : Ω), f ≠ 0 → ω ≠ 0 → smulΩ f ω ≠ 0)
    {D₁ D₂ : Div}
    (h₁ : IsCanonical divΩ D₁)
    (h₂ : LinearlyEquivalent divF D₁ D₂) :
    IsCanonical divΩ D₂ := by
  obtain ⟨ω₁, hω₁_ne, rfl⟩ := h₁
  obtain ⟨f, hf_ne, hf_eq⟩ := h₂
  exact ⟨smulΩ f ω₁, smul_ne_zero f ω₁ hf_ne hω₁_ne, by
    rw [hf_eq, div_smul_eq f ω₁ hf_ne hω₁_ne, add_comm]⟩

theorem canonical_divisors_form_single_class

    (omega_one_dim : ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 →
      ∃ f : F, f ≠ 0 ∧ ω₂ = smulΩ f ω₁)

    (div_smul_eq : ∀ (f : F) (ω : Ω), f ≠ 0 → ω ≠ 0 →
      divΩ (smulΩ f ω) = divF f + divΩ ω)

    (smul_ne_zero : ∀ (f : F) (ω : Ω), f ≠ 0 → ω ≠ 0 → smulΩ f ω ≠ 0)
    {D₁ D₂ : Div}
    (h₁ : IsCanonical divΩ D₁) :
    IsCanonical divΩ D₂ ↔ LinearlyEquivalent divF D₁ D₂ := by
  constructor
  · intro h₂
    exact canonical_linearlyEquivalent divF divΩ smulΩ omega_one_dim div_smul_eq h₁ h₂
  · intro h₂
    exact isCanonical_of_linearlyEquivalent divF divΩ smulΩ div_smul_eq smul_ne_zero h₁ h₂

theorem cor_22_19_weil_diff_same_div
    {k : Type*} [Field k] [Algebra k F]

    (omega_one_dim : ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 →
      ∃ f : F, f ≠ 0 ∧ ω₂ = smulΩ f ω₁)

    (div_smul_eq : ∀ (f : F) (ω : Ω), f ≠ 0 → ω ≠ 0 →
      divΩ (smulΩ f ω) = divF f + divΩ ω)


    (divF_zero_iff_const : ∀ (f : F), f ≠ 0 →
      (divF f = 0 ↔ ∃ c : k, c ≠ 0 ∧ algebraMap k F c = f))

    (divF_const_zero : ∀ (c : k), c ≠ 0 → divF (algebraMap k F c) = 0)
    {ω₁ ω₂ : Ω} (hω₁ : ω₁ ≠ 0) (hω₂ : ω₂ ≠ 0) :
    divΩ ω₁ = divΩ ω₂ ↔ ∃ c : k, c ≠ 0 ∧ ω₂ = smulΩ (algebraMap k F c) ω₁ := by
  constructor
  ·
    intro hdiv_eq

    obtain ⟨f, hf_ne, hf_eq⟩ := omega_one_dim ω₁ ω₂ hω₁ hω₂

    have h_divf_zero : divF f = 0 := by
      have h1 : divΩ ω₁ = divF f + divΩ ω₁ := by
        calc divΩ ω₁ = divΩ ω₂ := hdiv_eq
          _ = divΩ (smulΩ f ω₁) := by rw [hf_eq]
          _ = divF f + divΩ ω₁ := div_smul_eq f ω₁ hf_ne hω₁
      exact add_eq_right.mp h1.symm

    obtain ⟨c, hc_ne, hc_eq⟩ := (divF_zero_iff_const f hf_ne).mp h_divf_zero
    exact ⟨c, hc_ne, by rw [hf_eq, hc_eq]⟩
  ·
    rintro ⟨c, hc_ne, hc_eq⟩
    have hc_ne_F : algebraMap k F c ≠ 0 :=
      fun h => hc_ne ((algebraMap k F).injective (h.trans (map_zero _).symm))
    rw [hc_eq, div_smul_eq (algebraMap k F c) ω₁ hc_ne_F hω₁,
        divF_const_zero c hc_ne, zero_add]

end CanonicalDivisors
