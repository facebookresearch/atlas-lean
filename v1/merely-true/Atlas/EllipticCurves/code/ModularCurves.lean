/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Manifold

open scoped ContDiff

/-- Definition 18.4 (Complex structure): a `ComplexStructure` on a topological space
`X` is a `ChartedSpace ℂ X` together with the property that `X` is a real-analytic
manifold modelled on `ℂ` (i.e., the transition maps between charts are holomorphic). -/
class ComplexStructure (X : Type*) [TopologicalSpace X] extends ChartedSpace ℂ X where
  isManifold : IsManifold 𝓘(ℂ) ω X

attribute [instance] ComplexStructure.isManifold

/-- Definition 18.5 (Riemann surface): a Riemann surface is a connected Hausdorff
topological space equipped with a one-dimensional `ComplexStructure`. -/
class RiemannSurface (X : Type*) [TopologicalSpace X] extends ComplexStructure X where
  [t2 : T2Space X]
  [connected : ConnectedSpace X]

attribute [instance] RiemannSurface.t2
attribute [instance] RiemannSurface.connected

open Matrix.SpecialLinearGroup Matrix CongruenceSubgroup

open scoped MatrixGroups

namespace Def1811

/-- The reduction-mod-`N` group homomorphism `SL₂(ℤ) → SL₂(ℤ/Nℤ)`. -/
noncomputable def SL2_reductionMod (N : ℕ) : SL(2, ℤ) →* SL(2, ZMod N) :=
  SpecialLinearGroup.map (Int.castRingHom (ZMod N))

/-- Definition 18.11: the principal congruence subgroup `Γ(N) ⊆ SL₂(ℤ)`, consisting of
matrices congruent to the identity modulo `N`. -/
def PrincipalCongruenceSubgroup (N : ℕ) : Subgroup SL(2, ℤ) :=
  CongruenceSubgroup.Gamma N

/-- Membership criterion for `Γ(N)`: a matrix `γ ∈ SL₂(ℤ)` lies in `Γ(N)` iff its
entries reduce mod `N` to the identity matrix. -/
theorem mem_principalCongruenceSubgroup {N : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ PrincipalCongruenceSubgroup N ↔
      (γ 0 0 : ZMod N) = 1 ∧ (γ 0 1 : ZMod N) = 0 ∧
      (γ 1 0 : ZMod N) = 0 ∧ (γ 1 1 : ZMod N) = 1 :=
  CongruenceSubgroup.Gamma_mem

/-- The Hecke-type congruence subgroup `Γ₀(N) ⊆ SL₂(ℤ)` of matrices that are upper
triangular modulo `N`. -/
def CongruenceSubgroup0 (N : ℕ) : Subgroup SL(2, ℤ) :=
  CongruenceSubgroup.Gamma0 N

/-- The Hecke-type congruence subgroup `Γ₁(N) ⊆ SL₂(ℤ)` of matrices that are
upper-unitriangular modulo `N`. -/
def CongruenceSubgroup1 (N : ℕ) : Subgroup SL(2, ℤ) :=
  CongruenceSubgroup.Gamma1 N

/-- Membership criterion for `Γ₁(N)`: a matrix `A` lies in `Γ₁(N)` iff its diagonal
entries are `≡ 1 (mod N)` and its lower-left entry is `≡ 0 (mod N)`. -/
theorem mem_congruenceSubgroup1 (N : ℕ) (A : SL(2, ℤ)) :
    A ∈ CongruenceSubgroup1 N ↔
      (A 0 0 : ZMod N) = 1 ∧ (A 1 1 : ZMod N) = 1 ∧ (A 1 0 : ZMod N) = 0 :=
  CongruenceSubgroup.Gamma1_mem N A

/-- Inclusion `Γ(N) ⊆ Γ₁(N)`: every matrix congruent to the identity mod `N` is in
particular upper-unitriangular mod `N`. -/
theorem principalCongruenceSubgroup_le_congruenceSubgroup1 (N : ℕ) :
    PrincipalCongruenceSubgroup N ≤ CongruenceSubgroup1 N := by
  intro γ hγ
  rw [mem_principalCongruenceSubgroup] at hγ
  rw [mem_congruenceSubgroup1]
  exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

/-- Inclusion `Γ₁(N) ⊆ Γ₀(N)`. -/
theorem congruenceSubgroup1_le_congruenceSubgroup0 (N : ℕ) :
    CongruenceSubgroup1 N ≤ CongruenceSubgroup0 N :=
  CongruenceSubgroup.Gamma1_in_Gamma0 N

/-- Definition 18.11: a subgroup `H ⊆ SL₂(ℤ)` is a *congruence subgroup* if it
contains some principal congruence subgroup `Γ(N)`. -/
def IsCongruenceSubgroup (H : Subgroup SL(2, ℤ)) : Prop :=
  CongruenceSubgroup.IsCongruenceSubgroup H

/-- `Γ(N)` is itself a congruence subgroup (for `N ≠ 0`). -/
theorem isCongruenceSubgroup_principalCongruenceSubgroup (N : ℕ) [NeZero N] :
    IsCongruenceSubgroup (PrincipalCongruenceSubgroup N) :=
  CongruenceSubgroup.Gamma_is_cong_sub N

/-- `Γ₁(N)` is a congruence subgroup (for `N ≠ 0`). -/
theorem isCongruenceSubgroup_congruenceSubgroup1 (N : ℕ) [NeZero N] :
    IsCongruenceSubgroup (CongruenceSubgroup1 N) :=
  CongruenceSubgroup.Gamma1_is_congruence N

/-- `Γ₀(N)` is a congruence subgroup (for `N ≠ 0`). -/
theorem isCongruenceSubgroup_congruenceSubgroup0 (N : ℕ) [NeZero N] :
    IsCongruenceSubgroup (CongruenceSubgroup0 N) :=
  CongruenceSubgroup.Gamma0_is_congruence N

/-- The open modular curve `Y_Γ := Γ \ ℍ`, the quotient of the upper half-plane by a
congruence subgroup `Γ`. -/
noncomputable def ModularCurveOpen (Γ : Subgroup SL(2, ℤ)) : Type :=
  Quotient (MulAction.orbitRel Γ UpperHalfPlane)











end Def1811

section Def1915_Prerequisites

open Def1811

open scoped MatrixGroups

/-- Bundled assertion that `Γ(N)`, `Γ₁(N)`, and `Γ₀(N)` are all congruence subgroups. -/
theorem congruenceSubgroups_are_congruence (N : ℕ) [NeZero N] :
    Def1811.IsCongruenceSubgroup (PrincipalCongruenceSubgroup N) ∧
    Def1811.IsCongruenceSubgroup (CongruenceSubgroup1 N) ∧
    Def1811.IsCongruenceSubgroup (CongruenceSubgroup0 N) :=
  ⟨isCongruenceSubgroup_principalCongruenceSubgroup N,
   isCongruenceSubgroup_congruenceSubgroup1 N,
   isCongruenceSubgroup_congruenceSubgroup0 N⟩

end Def1915_Prerequisites

open Def1811

open scoped MatrixGroups







namespace SL2Stabilizer

open ModularGroup

/-- The cube root of unity `ρ = -1/2 + i√3/2 ∈ ℍ`, one of the two elliptic points
(along with `i`) in the standard fundamental domain `𝓕`. -/
noncomputable def ρ : UpperHalfPlane :=
  ⟨-1/2 + Complex.I * (Real.sqrt 3 / 2), by
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_re]⟩

/-- The translate `ρ' = ρ + 1 = 1/2 + i√3/2 ∈ ℍ`, the other corner of the fundamental
domain `𝓕`. -/
noncomputable def ρ' : UpperHalfPlane := (1 : ℝ) +ᵥ ρ







end SL2Stabilizer

section Lemma181

open ModularGroup UpperHalfPlane Complex Set Matrix SpecialLinearGroup
open scoped MatrixGroups

set_option maxHeartbeats 1600000

/-- Auxiliary lemma: the set of integers `n` with `n² ≤ N` is finite (it is contained
in `[-⌈√N⌉, ⌈√N⌉]`). Used in the proof of Lemma 18.1 to bound matrix entries. -/
lemma int_sq_bounded_finite (N : ℝ) : Set.Finite {n : ℤ | (n : ℝ) ^ 2 ≤ N} := by
  by_cases hN : 0 ≤ N
  · apply Set.Finite.subset (Set.finite_Icc (-⌈Real.sqrt N⌉) ⌈Real.sqrt N⌉)
    intro n hn; simp only [Set.mem_setOf_eq] at hn
    have : |(n : ℝ)| ≤ (⌈Real.sqrt N⌉ : ℝ) :=
      ((Real.sqrt_sq_eq_abs ↑n ▸ Real.sqrt_le_sqrt hn).trans (Int.le_ceil _))
    rw [Set.mem_Icc]
    exact ⟨by exact_mod_cast (show -(⌈Real.sqrt N⌉ : ℝ) ≤ (n : ℝ) by linarith [neg_abs_le (n : ℝ)]),
           by exact_mod_cast (show (n : ℝ) ≤ (⌈Real.sqrt N⌉ : ℝ) by linarith [le_abs_self (n : ℝ)])⟩
  · push Not at hN; convert Set.finite_empty; ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    linarith [sq_nonneg (n : ℝ)]

/-- The classical identity `|cz + d|² = Im(z) / Im(γz)` for `γ = ((a,b),(c,d)) ∈ SL₂(ℤ)`
acting on the upper half-plane. -/
lemma normSq_denom_eq_im_div (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    Complex.normSq (UpperHalfPlane.denom
      (SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (z : ℂ)) =
    z.im / (g • z).im := by
  have him := ModularGroup.im_smul_eq_div_normSq g z
  have hgz_pos : 0 < (g • z).im := (g • z).coe_im_pos
  have hns_pos : 0 < Complex.normSq (UpperHalfPlane.denom
      (SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (z : ℂ)) := by
    rw [Complex.normSq_pos]; exact UpperHalfPlane.denom_ne_zero _ z
  rw [him]; field_simp

/-- Expansion of `|cz + d|² = (c·Re(z) + d)² + (c·Im(z))²` as a sum of two squares of
real numbers, used to extract bounds on the matrix entries `c, d`. -/
lemma normSq_denom_expand (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    Complex.normSq (UpperHalfPlane.denom
      (SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (z : ℂ)) =
    (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * z.re +
     ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ))^2 +
    (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * z.im)^2 := by
  rw [ModularGroup.denom_apply]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im]
  simp; ring

/-- Lemma 18.1: for any compact sets `A, B ⊆ ℍ`, the set of `γ ∈ SL₂(ℤ)` such that
`γA ∩ B ≠ ∅` is finite. Proved by bounding the four entries `a, b, c, d` of `γ`
using `|cτ + d|² = Im(τ)/Im(γτ)` and the compactness of `A, B`. -/
theorem lemma_18_1 (A B : Set UpperHalfPlane)
    (hA : IsCompact A) (hB : IsCompact B) :
    Set.Finite {γ : SL(2, ℤ) | ∃ τ ∈ A, γ • τ ∈ B} := by

  by_cases hAne : A.Nonempty
  · by_cases hBne : B.Nonempty
    ·
      obtain ⟨R_A, m_A, hm_A, hA_strip⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hA

      obtain ⟨_, m_B, hm_B, hB_strip⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hB

      obtain ⟨τ_max, hτ_max_mem, hτ_max⟩ :=
        hA.exists_isMaxOn hAne continuous_im.continuousOn
      set M_A := τ_max.im

      have hB_cpt : IsCompact (UpperHalfPlane.coe '' B) := hB.image continuous_coe
      obtain ⟨z_max, ⟨τ_z, hτ_z_mem, hτ_z_eq⟩, hz_max⟩ :=
        hB_cpt.exists_isMaxOn (hBne.image _) Complex.continuous_normSq.continuousOn
      set M_nsq_B := Complex.normSq z_max

      set r := M_A / m_B

      set N := max (max (r / m_A ^ 2) (2 * r + 2 * (r / m_A ^ 2) * R_A ^ 2))
                   (max (M_nsq_B * r / m_A ^ 2)
                        (2 * M_nsq_B * r + 2 * (M_nsq_B * r / m_A ^ 2) * R_A ^ 2))

      let entries : SL(2, ℤ) → ℤ × ℤ × ℤ × ℤ := fun γ =>
        ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
         (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)
      have h_inj : Function.Injective entries := by
        intro γ₁ γ₂ h; simp only [entries, Prod.mk.injEq] at h; ext i j
        fin_cases i <;> fin_cases j <;>
          [exact h.1; exact h.2.1; exact h.2.2.1; exact h.2.2.2]

      set target : Set (ℤ × ℤ × ℤ × ℤ) := {abcd |
          (abcd.1 : ℝ)^2 ≤ N ∧ (abcd.2.1 : ℝ)^2 ≤ N ∧
          (abcd.2.2.1 : ℝ)^2 ≤ N ∧ (abcd.2.2.2 : ℝ)^2 ≤ N}
      have h_target_finite : target.Finite :=
        Set.Finite.subset
          ((int_sq_bounded_finite N).prod ((int_sq_bounded_finite N).prod
            ((int_sq_bounded_finite N).prod (int_sq_bounded_finite N))))
          (fun ⟨a, b, c, d⟩ ⟨ha, hb, hc, hd⟩ => ⟨ha, hb, hc, hd⟩)

      suffices h_sub : {γ : SL(2, ℤ) | ∃ τ ∈ A, γ • τ ∈ B} ⊆ entries ⁻¹' target by
        exact Set.Finite.subset (h_target_finite.preimage h_inj.injOn) h_sub

      intro γ ⟨τ, hτA, hgτB⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq, target, entries]

      have hτ_strip := hA_strip hτA
      have hgτ_strip := hB_strip hgτB
      simp only [UpperHalfPlane.verticalStrip, Set.mem_setOf_eq] at hτ_strip hgτ_strip
      have hτ_im_ge : m_A ≤ τ.im := hτ_strip.2
      have hτ_re_le : |τ.re| ≤ R_A := hτ_strip.1
      have hgτ_im_ge : m_B ≤ (γ • τ).im := hgτ_strip.2
      have hτ_im_le : τ.im ≤ M_A := hτ_max hτA

      have h_nsq_le : Complex.normSq (UpperHalfPlane.denom
          (SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
          (τ : ℂ)) ≤ r := by
        rw [normSq_denom_eq_im_div]
        have h_gτ_im_pos : 0 < (γ • τ).im := (γ • τ).coe_im_pos
        rw [div_le_div_iff₀ h_gτ_im_pos hm_B]
        exact mul_le_mul_of_nonneg_right hτ_im_le (le_of_lt hm_B) |>.trans
          (mul_le_mul_of_nonneg_left hgτ_im_ge (le_of_lt τ_max.coe_im_pos))

      have h_expand := normSq_denom_expand γ τ
      set c_real := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ)
      set d_real := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ)
      set a_real := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ)
      set b_real := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ)

      have h_c_im_sq : (c_real * τ.im)^2 ≤ r := by
        calc (c_real * τ.im)^2
            ≤ (c_real * τ.re + d_real)^2 + (c_real * τ.im)^2 := le_add_of_nonneg_left (sq_nonneg _)
          _ = _ := h_expand.symm
          _ ≤ r := h_nsq_le

      have h_cd_re_sq : (c_real * τ.re + d_real)^2 ≤ r := by
        calc (c_real * τ.re + d_real)^2
            ≤ (c_real * τ.re + d_real)^2 + (c_real * τ.im)^2 := le_add_of_nonneg_right (sq_nonneg _)
          _ = _ := h_expand.symm
          _ ≤ r := h_nsq_le

      have h_c_sq : c_real^2 ≤ r / m_A^2 := by
        have h2 : c_real^2 * τ.im^2 ≤ r := by nlinarith
        have h3 : c_real^2 * m_A^2 ≤ c_real^2 * τ.im^2 :=
          mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith) hτ_im_ge) (sq_nonneg _)
        rw [le_div_iff₀ (by positivity : 0 < m_A^2)]; linarith

      have h_d_sq : d_real^2 ≤ 2 * r + 2 * (r / m_A^2) * R_A^2 := by
        have : d_real = (c_real * τ.re + d_real) - c_real * τ.re := by ring
        rw [this]
        calc ((c_real * τ.re + d_real) - c_real * τ.re)^2
            ≤ 2 * (c_real * τ.re + d_real)^2 + 2 * (c_real * τ.re)^2 := by
                have := sq_nonneg ((c_real * τ.re + d_real) + c_real * τ.re)
                nlinarith [sq_nonneg ((c_real * τ.re + d_real) - c_real * τ.re)]
          _ ≤ 2 * r + 2 * (c_real^2 * τ.re^2) := by nlinarith
          _ ≤ 2 * r + 2 * (r / m_A^2 * R_A^2) := by
              have : c_real^2 * τ.re^2 ≤ r / m_A^2 * R_A^2 := by
                apply mul_le_mul h_c_sq _ (sq_nonneg _) (by positivity)
                calc τ.re^2 ≤ |τ.re|^2 := le_of_eq (sq_abs _).symm
                  _ ≤ R_A^2 := by nlinarith [abs_nonneg τ.re]
              linarith
          _ = 2 * r + 2 * (r / m_A ^ 2) * R_A ^ 2 := by ring


      have h_gτ_nsq_le : Complex.normSq (γ • τ : UpperHalfPlane) ≤ M_nsq_B := by
        exact hz_max (Set.mem_image_of_mem _ hgτB)
      have hdenom_ne' : (c_real : ℂ) * (τ : ℂ) + (d_real : ℂ) ≠ 0 := by
        have := UpperHalfPlane.denom_ne_zero
          (SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) τ
        rw [ModularGroup.denom_apply] at this
        convert this using 1
      have h_num_denom : (a_real : ℂ) * (τ : ℂ) + (b_real : ℂ) =
          ((γ • τ : UpperHalfPlane) : ℂ) *
          ((c_real : ℂ) * (τ : ℂ) + (d_real : ℂ)) := by
        have hcoe := UpperHalfPlane.coe_specialLinearGroup_apply γ τ
        have : ((γ • τ : UpperHalfPlane) : ℂ) =
            ((a_real : ℂ) * (τ : ℂ) + (b_real : ℂ)) /
            ((c_real : ℂ) * (τ : ℂ) + (d_real : ℂ)) := by
          rw [hcoe]
          congr 1 <;> ring
        rw [this, div_mul_cancel₀ _ hdenom_ne']
      have h_nsq_num : Complex.normSq ((a_real : ℂ) * (τ : ℂ) + (b_real : ℂ)) ≤ M_nsq_B * r := by
        rw [h_num_denom, map_mul]
        apply mul_le_mul h_gτ_nsq_le _ (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
        exact h_nsq_le

      have h_num_expand : Complex.normSq ((a_real : ℂ) * (τ : ℂ) + (b_real : ℂ)) =
          (a_real * τ.re + b_real)^2 + (a_real * τ.im)^2 := by
        simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
          Complex.add_re, Complex.add_im]; ring

      have h_a_sq : a_real^2 ≤ M_nsq_B * r / m_A^2 := by
        have h1 : (a_real * τ.im)^2 ≤ M_nsq_B * r := by
          calc (a_real * τ.im)^2
              ≤ (a_real * τ.re + b_real)^2 + (a_real * τ.im)^2 := le_add_of_nonneg_left (sq_nonneg _)
            _ = _ := h_num_expand.symm
            _ ≤ M_nsq_B * r := h_nsq_num
        have h2 : a_real^2 * τ.im^2 ≤ M_nsq_B * r := by nlinarith
        have h3 : a_real^2 * m_A^2 ≤ a_real^2 * τ.im^2 :=
          mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith) hτ_im_ge) (sq_nonneg _)
        rw [le_div_iff₀ (by positivity : 0 < m_A^2)]; linarith

      have h_b_sq : b_real^2 ≤ 2 * M_nsq_B * r + 2 * (M_nsq_B * r / m_A^2) * R_A^2 := by
        have h_ab_re_sq : (a_real * τ.re + b_real)^2 ≤ M_nsq_B * r := by
          calc (a_real * τ.re + b_real)^2
              ≤ (a_real * τ.re + b_real)^2 + (a_real * τ.im)^2 := le_add_of_nonneg_right (sq_nonneg _)
            _ = _ := h_num_expand.symm
            _ ≤ M_nsq_B * r := h_nsq_num
        have : b_real = (a_real * τ.re + b_real) - a_real * τ.re := by ring
        rw [this]
        calc ((a_real * τ.re + b_real) - a_real * τ.re)^2
            ≤ 2 * (a_real * τ.re + b_real)^2 + 2 * (a_real * τ.re)^2 := by
                have := sq_nonneg ((a_real * τ.re + b_real) + a_real * τ.re)
                nlinarith [sq_nonneg ((a_real * τ.re + b_real) - a_real * τ.re)]
          _ ≤ 2 * (M_nsq_B * r) + 2 * (a_real^2 * τ.re^2) := by nlinarith
          _ ≤ 2 * (M_nsq_B * r) + 2 * (M_nsq_B * r / m_A^2 * R_A^2) := by
              have : a_real^2 * τ.re^2 ≤ M_nsq_B * r / m_A^2 * R_A^2 := by
                have hr_nn : 0 ≤ r := div_nonneg (le_of_lt τ_max.coe_im_pos) hm_B.le
                apply mul_le_mul h_a_sq _ (sq_nonneg _) (div_nonneg (mul_nonneg (Complex.normSq_nonneg _) hr_nn) (sq_nonneg _))
                calc τ.re^2 ≤ |τ.re|^2 := le_of_eq (sq_abs _).symm
                  _ ≤ R_A^2 := by nlinarith [abs_nonneg τ.re]
              linarith
          _ = 2 * M_nsq_B * r + 2 * (M_nsq_B * r / m_A ^ 2) * R_A ^ 2 := by ring

      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [a_real, b_real, c_real, d_real]
      ·
        calc (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ))^2
            = a_real^2 := rfl
          _ ≤ M_nsq_B * r / m_A^2 := h_a_sq
          _ ≤ N := le_max_of_le_right (le_max_left _ _)
      ·
        calc (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ))^2
            = b_real^2 := rfl
          _ ≤ 2 * M_nsq_B * r + 2 * (M_nsq_B * r / m_A^2) * R_A^2 := h_b_sq
          _ ≤ N := le_max_of_le_right (le_max_right _ _)
      ·
        calc (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ))^2
            = c_real^2 := rfl
          _ ≤ r / m_A^2 := h_c_sq
          _ ≤ N := le_max_of_le_left (le_max_left _ _)
      ·
        calc (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ))^2
            = d_real^2 := rfl
          _ ≤ 2 * r + 2 * (r / m_A^2) * R_A^2 := h_d_sq
          _ ≤ N := le_max_of_le_left (le_max_right _ _)
    ·
      convert Set.finite_empty; ext γ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro ⟨τ, _, hτB⟩; exact hBne ⟨γ • τ, hτB⟩
  ·
    convert Set.finite_empty; ext γ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro ⟨τ, hτA, _⟩; exact hAne ⟨τ, hτA⟩

end Lemma181

open Complex Metric Set Function

/-- If `f` maps `ball 0 R` into itself, then so does its `k`-th iterate. -/
lemma iterate_mem_ball_of_mapsTo {R : ℝ} {f : ℂ → ℂ}
    (hf_maps : MapsTo f (ball (0 : ℂ) R) (ball (0 : ℂ) R))
    (k : ℕ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    (f^[k]) z ∈ ball (0 : ℂ) R := by
  induction k with
  | zero => exact hz
  | succ k ih => rw [iterate_succ', Function.comp_apply]; exact hf_maps ih

/-- If `f(z) = ζ·z` on `ball 0 R` and `f` maps the ball to itself, then
`f^k(z) = ζ^k · z` for every iterate. -/
lemma iterate_eq_pow_mul_on_ball {ζ : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hf_maps : MapsTo f (ball (0 : ℂ) R) (ball (0 : ℂ) R))
    (hf_eq : ∀ z ∈ ball (0 : ℂ) R, f z = ζ * z)
    (k : ℕ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    (f^[k]) z = ζ ^ k * z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ', Function.comp_apply,
      hf_eq _ (iterate_mem_ball_of_mapsTo hf_maps k hz), ih]
    ring

/-- Schwarz lemma / disk-automorphism rigidity: any holomorphic self-map of an open
disk fixing the origin that admits a holomorphic inverse (also fixing 0) must be a
rotation `z ↦ ζz` for some unimodular `ζ`. -/
theorem disk_aut_fixing_origin_is_rotation {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ}
    (hf_diff : DifferentiableOn ℂ f (ball 0 R))
    (hf_maps : MapsTo f (ball 0 R) (ball 0 R))
    (hf_zero : f 0 = 0)
    (hg_diff : DifferentiableOn ℂ g (ball 0 R))
    (hg_maps : MapsTo g (ball 0 R) (ball 0 R))
    (hg_zero : g 0 = 0)
    (hgf : ∀ z ∈ ball (0 : ℂ) R, g (f z) = z) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) R, f z = ζ * z := by
  have hf_maps' : MapsTo f (ball 0 R) (closedBall 0 R) :=
    hf_maps.mono_right ball_subset_closedBall
  have hg_maps' : MapsTo g (ball 0 R) (closedBall 0 R) :=
    hg_maps.mono_right ball_subset_closedBall

  have hnorm_eq : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ = ‖z‖ := by
    intro z hz
    have hz' := mem_ball_zero_iff.mp hz
    have hfz' := mem_ball_zero_iff.mp (hf_maps hz)
    have h1 := Complex.norm_le_norm_of_mapsTo_ball hf_diff hf_maps' hf_zero hz'
    have h2 := Complex.norm_le_norm_of_mapsTo_ball hg_diff hg_maps' hg_zero hfz'
    rw [hgf z hz] at h2; linarith

  have ⟨z₀, hz₀, hz₀_ne⟩ : ∃ z₀ ∈ ball (0 : ℂ) R, z₀ ≠ 0 := by
    refine ⟨↑(R / 2), ?_, ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : R / 2 > 0)]
      linarith
    · simp [hR.ne']

  have hdslope_eq : ‖dslope f 0 z₀‖ = R / R := by
    rw [div_self hR.ne', dslope_of_ne _ hz₀_ne, slope_def_module]
    simp only [hf_zero, sub_zero, norm_smul, norm_inv, hnorm_eq z₀ hz₀]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz₀_ne)

  have hf_maps'' : MapsTo f (ball 0 R) (closedBall (f 0) R) := by rwa [hf_zero]
  obtain ⟨ζ, hζ_norm, hζ_eq⟩ :=
    Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div' hf_diff hf_maps''
      ⟨z₀, hz₀, hdslope_eq⟩
  rw [div_self hR.ne'] at hζ_norm
  refine ⟨ζ, hζ_norm, fun z hz => ?_⟩
  have := hζ_eq hz
  simp only [hf_zero, sub_zero, zero_add, smul_eq_mul] at this
  rw [this, mul_comm]

/-- Strengthening of the rotation lemma: if additionally `f^n = id` on the ball with
`n` minimal, then the rotation constant `ζ` is a *primitive* `n`-th root of unity.
This is the analytic core used in proving Lemma 18.8. -/
theorem disk_aut_primitive_root {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ} {n : ℕ} (hn : 0 < n)
    (hf_diff : DifferentiableOn ℂ f (ball 0 R))
    (hf_maps : MapsTo f (ball 0 R) (ball 0 R))
    (hf_zero : f 0 = 0)
    (hg_diff : DifferentiableOn ℂ g (ball 0 R))
    (hg_maps : MapsTo g (ball 0 R) (ball 0 R))
    (hg_zero : g 0 = 0)
    (hgf : ∀ z ∈ ball (0 : ℂ) R, g (f z) = z)
    (hiter : ∀ z ∈ ball (0 : ℂ) R, (f^[n]) z = z)
    (hmin : ∀ k : ℕ, 0 < k → k < n → ∃ z ∈ ball (0 : ℂ) R, (f^[k]) z ≠ z) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ n ∧ ∀ z ∈ ball (0 : ℂ) R, f z = ζ * z := by

  obtain ⟨ζ, _, hf_eq⟩ := disk_aut_fixing_origin_is_rotation hR hf_diff hf_maps hf_zero
    hg_diff hg_maps hg_zero hgf

  have ⟨z₀, hz₀, hz₀_ne⟩ : ∃ z₀ ∈ ball (0 : ℂ) R, z₀ ≠ 0 := by
    refine ⟨↑(R / 2), ?_, ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : R / 2 > 0)]
      linarith
    · simp [hR.ne']

  have hζ_pow : ζ ^ n = 1 := by
    have h := hiter z₀ hz₀
    rw [iterate_eq_pow_mul_on_ball hf_maps hf_eq n hz₀] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp (by linear_combination h)).resolve_right hz₀_ne)

  exact ⟨ζ, ⟨hζ_pow, fun l hl => by
    by_contra h_ndvd
    have hmod_pos : 0 < l % n := by omega
    have hmod_lt : l % n < n := Nat.mod_lt l hn
    obtain ⟨w, hw, hw_ne⟩ := hmin (l % n) hmod_pos hmod_lt
    apply hw_ne
    rw [iterate_eq_pow_mul_on_ball hf_maps hf_eq (l % n) hw]
    have : ζ ^ (l % n) = 1 := by
      rw [← Nat.div_add_mod l n] at hl
      rw [pow_add, pow_mul, hζ_pow, one_pow, one_mul] at hl
      exact hl
    rw [this, one_mul]⟩, hf_eq⟩

open scoped UpperHalfPlane

/-- The Cayley-type uniformizer `δ_x(τ) = (τ - τ_x)/(τ - conj(τ_x))` mapping the upper
half-plane biholomorphically to the open unit disk, sending `τ_x ↦ 0`. Used in
Lemma 18.8 to transfer disk automorphism rigidity to the upper half-plane. -/
noncomputable def deltaMap (τ_x : ℍ) (τ : ℂ) : ℂ :=
  (τ - (τ_x : ℂ)) / (τ - starRingEnd ℂ (τ_x : ℂ))

/-- Lemma 18.8: let `τ_x ∈ ℍ` and `φ : ℍ → ℍ` be holomorphic with `φ(τ_x) = τ_x` and
`φ^n = id` with `n` minimal. Then there exists a primitive `n`-th root of unity `ζ`
such that `δ_x(φ(τ)) = ζ · δ_x(τ)` for every `τ ∈ ℍ`. Proved by conjugating with the
Cayley-type map `deltaMap` and applying `disk_aut_primitive_root`. -/
theorem lemma_18_8 (τ_x : ℍ)
    {φ : ℍ → ℍ} {n : ℕ} (hn : 0 < n)
    (hφ_fix : φ τ_x = τ_x)
    (hφ_iter : ∀ τ : ℍ, (φ^[n]) τ = τ)
    (hφ_min : ∀ k : ℕ, 0 < k → k < n → ∃ τ : ℍ, (φ^[k]) τ ≠ τ)

    {f g : ℂ → ℂ}
    (hf_diff : DifferentiableOn ℂ f (ball 0 1))
    (hf_maps : MapsTo f (ball 0 1) (ball 0 1))
    (hf_zero : f 0 = 0)
    (hg_diff : DifferentiableOn ℂ g (ball 0 1))
    (hg_maps : MapsTo g (ball 0 1) (ball 0 1))
    (hg_zero : g 0 = 0)
    (hgf : ∀ z ∈ ball (0 : ℂ) 1, g (f z) = z)

    (hf_compat : ∀ τ : ℍ, f (deltaMap τ_x (τ : ℂ)) = deltaMap τ_x (φ τ : ℂ))

    (hδ_maps : ∀ τ : ℍ, deltaMap τ_x (τ : ℂ) ∈ ball (0 : ℂ) 1)


    (hf_iter : ∀ z ∈ ball (0 : ℂ) 1, (f^[n]) z = z)
    (hf_min : ∀ k : ℕ, 0 < k → k < n → ∃ z ∈ ball (0 : ℂ) 1, (f^[k]) z ≠ z) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ n ∧
      ∀ τ : ℍ, deltaMap τ_x (φ τ : ℂ) = ζ * deltaMap τ_x (τ : ℂ) := by

  obtain ⟨ζ, hζ_prim, hf_eq⟩ := disk_aut_primitive_root one_pos hn
    hf_diff hf_maps hf_zero hg_diff hg_maps hg_zero hgf hf_iter hf_min
  exact ⟨ζ, hζ_prim, fun τ => by rw [← hf_compat τ]; exact hf_eq (deltaMap τ_x (τ : ℂ)) (hδ_maps τ)⟩

section Lemma182

open Set

open scoped MatrixGroups

/-- The action map `τ ↦ γ • τ` on the upper half-plane is continuous for every
`γ ∈ SL₂(ℤ)`. -/
lemma sl2z_continuous_smul (γ : SL(2, ℤ)) :
    Continuous (fun z : UpperHalfPlane => γ • z) := by
  change Continuous (fun z : UpperHalfPlane =>
    (Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ)) • z)
  exact continuous_const_smul _

set_option maxHeartbeats 1600000

/-- Lemma 18.2: for any `τ₁, τ₂ ∈ ℍ*`, there exist open neighborhoods `U₁, U₂` of
`τ₁, τ₂` such that for every `γ ∈ SL₂(ℤ)`, some `z ∈ U₁` has `γ•z ∈ U₂` iff
`γ•τ₁ = τ₂`. In particular each `τ` has a neighborhood in which it is the unique
representative of its `Γ`-orbit. -/
theorem lemma_18_2 (τ₁ τ₂ : UpperHalfPlane) :
    ∃ U₁ U₂ : Set UpperHalfPlane, IsOpen U₁ ∧ IsOpen U₂ ∧ τ₁ ∈ U₁ ∧ τ₂ ∈ U₂ ∧
      ∀ γ : SL(2, ℤ), (∃ z ∈ U₁, γ • z ∈ U₂) ↔ γ • τ₁ = τ₂ := by

  obtain ⟨K₁, hK₁_compact, hK₁_nhds⟩ := exists_compact_mem_nhds τ₁
  obtain ⟨K₂, hK₂_compact, hK₂_nhds⟩ := exists_compact_mem_nhds τ₂


  have hS_finite : Set.Finite {γ : SL(2, ℤ) | (∃ τ ∈ K₁, γ • τ ∈ K₂) ∧ γ • τ₁ ≠ τ₂} :=
    (lemma_18_1 K₁ K₂ hK₁_compact hK₂_compact).subset (fun γ hγ => hγ.1)
  set S := hS_finite.toFinset

  have hsep : ∀ γ ∈ S, ∃ V W : Set UpperHalfPlane,
      IsOpen V ∧ IsOpen W ∧ γ • τ₁ ∈ V ∧ τ₂ ∈ W ∧ Disjoint V W := by
    intro γ hγ
    have := (Set.Finite.mem_toFinset hS_finite).mp hγ
    exact t2_separation this.2

  classical
  let V : SL(2, ℤ) → Set UpperHalfPlane := fun γ =>
    if h : γ ∈ S then (hsep γ h).choose else Set.univ
  let W : SL(2, ℤ) → Set UpperHalfPlane := fun γ =>
    if h : γ ∈ S then (hsep γ h).choose_spec.choose else Set.univ
  have hV : ∀ γ (h : γ ∈ S), IsOpen (V γ) ∧ γ • τ₁ ∈ V γ := by
    intro γ hγ; simp only [V, dif_pos hγ]
    exact ⟨(hsep γ hγ).choose_spec.choose_spec.1,
           (hsep γ hγ).choose_spec.choose_spec.2.2.1⟩
  have hW : ∀ γ (h : γ ∈ S), IsOpen (W γ) ∧ τ₂ ∈ W γ := by
    intro γ hγ; simp only [W, dif_pos hγ]
    exact ⟨(hsep γ hγ).choose_spec.choose_spec.2.1,
           (hsep γ hγ).choose_spec.choose_spec.2.2.2.1⟩
  have hVW_disj : ∀ γ (h : γ ∈ S), Disjoint (V γ) (W γ) := by
    intro γ hγ; simp only [V, W, dif_pos hγ]
    exact (hsep γ hγ).choose_spec.choose_spec.2.2.2.2


  let U₁ := interior K₁ ∩ ⋂ γ ∈ (S : Set SL(2, ℤ)), (fun z => γ • z) ⁻¹' V γ
  let U₂ := interior K₂ ∩ ⋂ γ ∈ (S : Set SL(2, ℤ)), W γ
  have hU₁_open : IsOpen U₁ := by
    apply IsOpen.inter isOpen_interior
    apply isOpen_biInter_finset
    intro γ hγ; exact (hV γ hγ).1.preimage (sl2z_continuous_smul γ)
  have hU₂_open : IsOpen U₂ := by
    apply IsOpen.inter isOpen_interior
    apply isOpen_biInter_finset
    intro γ hγ; exact (hW γ hγ).1
  have hτ₁_mem : τ₁ ∈ U₁ :=
    ⟨mem_interior_iff_mem_nhds.mpr hK₁_nhds, by
      simp only [mem_iInter]; intro γ hγ; exact mem_preimage.mpr (hV γ hγ).2⟩
  have hτ₂_mem : τ₂ ∈ U₂ :=
    ⟨mem_interior_iff_mem_nhds.mpr hK₂_nhds, by
      simp only [mem_iInter]; intro γ hγ; exact (hW γ hγ).2⟩
  refine ⟨U₁, U₂, hU₁_open, hU₂_open, hτ₁_mem, hτ₂_mem, fun γ => ?_⟩
  constructor
  ·
    rintro ⟨z, ⟨hz_K₁, hz_V⟩, hgz_K₂, hgz_W⟩

    by_cases hγ : γ ∈ S
    ·
      have hz_in_V : γ • z ∈ V γ := by
        simp only [mem_iInter] at hz_V; exact hz_V γ hγ
      have hgz_in_W : γ • z ∈ W γ := by
        simp only [mem_iInter] at hgz_W; exact hgz_W γ hγ
      exact absurd (Set.disjoint_iff.mp (hVW_disj γ hγ) ⟨hz_in_V, hgz_in_W⟩) id
    ·

      rw [Set.Finite.mem_toFinset] at hγ
      simp only [Set.mem_setOf_eq] at hγ
      by_contra h
      exact hγ ⟨⟨z, interior_subset hz_K₁, interior_subset hgz_K₂⟩, h⟩
  ·
    intro heq
    exact ⟨τ₁, hτ₁_mem, heq ▸ hτ₂_mem⟩

end Lemma182

section Theorem189

open Manifold Def1811

open scoped MatrixGroups






end Theorem189

section Theorem1810

open Manifold Def1811

open scoped MatrixGroups

/-- A combinatorial triangulation of a topological space, recording the number of
vertices `V`, edges `E`, faces `F`, and genus `g`, subject to the Euler characteristic
identity `V - E + F = 2 - 2g`. -/
structure Triangulation (X : Type*) [TopologicalSpace X] where
  V : ℕ
  E : ℕ
  F : ℕ
  g : ℕ
  euler : V + F + 2 * g = E + 2








end Theorem1810
