/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Ch22WeberLFunction
import Atlas.NumberTheoryI.code.AnalyticClassNumber
import Atlas.NumberTheoryI.code.Cor1838
noncomputable section

open scoped NumberField
open Complex Finset Section19

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

def halfPlane (K : Type u) [Field K] [NumberField K] : Set ℂ :=
  {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re}





def rayClassPartialZeta_residue_val {𝔪 : Modulus K}
    (_γ : RayClassGroup K 𝔪) : ℂ :=
  (NumberField.dedekindZeta_residue K : ℂ) / (Fintype.card (RayClassGroup K 𝔪) : ℂ)

theorem rayClassPartialZeta_residue_val_ne_zero {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) : rayClassPartialZeta_residue_val γ ≠ 0 := by
  unfold rayClassPartialZeta_residue_val
  apply div_ne_zero
  · exact_mod_cast NumberField.dedekindZeta_residue_ne_zero K
  · exact_mod_cast Fintype.card_ne_zero








lemma halfPlane_exponent_nonneg :
    (0 : ℝ) ≤ 1 - 1 / (Module.finrank ℚ K : ℝ) := by
  have hn : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  have h1 : 1 / (Module.finrank ℚ K : ℝ) ≤ 1 := by
    rw [div_le_one hn]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp Module.finrank_pos)
  linarith

lemma halfPlane_exponent_lt_one :
    1 - 1 / (Module.finrank ℚ K : ℝ) < 1 := by
  have hn : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  linarith [div_pos one_pos hn]



def rayClassPartialZeta_residue (𝔪 : Modulus K) : ℂ :=
  (NumberField.dedekindZeta_residue K : ℂ) / (Fintype.card (RayClassGroup K 𝔪) : ℂ)














theorem sum_nonprincipal_char_eq_zero
    {𝔪 : Modulus K} (χ : RayClassChar K 𝔪)
    (hχ : ¬χ.IsPrincipal) :
    ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) = 0 := by

  simp only [RayClassChar.IsPrincipal, not_forall] at hχ
  obtain ⟨g₀, hg₀⟩ := hχ

  have key : (χ g₀ : ℂ) * ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) =
      ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) := by
    rw [Finset.mul_sum]
    have heq : (fun γ : RayClassGroup K 𝔪 => (χ g₀ : ℂ) * (χ γ : ℂ)) =
        (fun γ : RayClassGroup K 𝔪 => (χ (g₀ * γ) : ℂ)) := by
      ext γ
      simp only [map_mul, Units.val_mul]
    rw [heq]
    exact Fintype.sum_bijective (fun γ => g₀ * γ) (Group.mulLeft_bijective g₀) _ _ (fun γ => rfl)

  have hne : (χ g₀ : ℂ) ≠ 1 := by
    intro h
    apply hg₀
    exact Units.ext h

  have hsub : ((χ g₀ : ℂ) - 1) * ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) = 0 := by
    rw [sub_mul, one_mul, key, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne)


structure WeberLFunction_MeromorphicExtension
    (𝔪 : Modulus K) (χ : RayClassChar K 𝔪) where
  toFun : ℂ → ℂ
  eq_on_convergence : ∀ s : ℂ, 1 < s.re →
    toFun s = WeberLFunction K 𝔪 χ s
  meromorphicOn : MeromorphicOn toFun (halfPlane K)
  simple_pole_at_one : ∃ v : ℂ,
    AnalyticAt ℂ (Function.update (fun s => (s - 1) * toFun s) 1 v) 1

  holomorphic_at_one_of_nonprincipal : ¬χ.IsPrincipal → AnalyticAt ℂ toFun 1







end RayClassField
