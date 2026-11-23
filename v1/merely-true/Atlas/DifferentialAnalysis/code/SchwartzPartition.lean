/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.Support
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section

open scoped SchwartzMap Manifold
open Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℝ E]

namespace TemperedDistribution

/-- Schwartz partition-of-unity vanishing principle: a tempered distribution `u` annihilates
any compactly supported Schwartz function `ψ` provided `u` vanishes locally everywhere, i.e.
for every point `x` there is an open neighbourhood `s ∋ x` such that `u` is vanishing on `s`.
The proof glues local vanishing via a smooth partition of unity subordinate to the cover. -/
theorem schwartz_partition_of_unity_vanishing
    (u : 𝓢'(E, F))
    (h_local : ∀ x : E, ∃ s : Set E, IsVanishingOn (⇑u) s ∧ IsOpen s ∧ x ∈ s)
    (ψ : 𝓢(E, ℂ)) (hψ : HasCompactSupport ψ) : u ψ = 0 := by

  choose S hS_van hS_open hS_mem using h_local

  have hcov : Set.univ ⊆ ⋃ x, S x := fun x _ => Set.mem_iUnion.mpr ⟨x, hS_mem x⟩
  obtain ⟨ρ, hρ_sub⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, E) isClosed_univ S hS_open hcov

  have hlf := ρ.locallyFinite
  have hfin : {i | (Function.support (⇑(ρ i)) ∩ tsupport (⇑ψ)).Nonempty}.Finite :=
    hlf.finite_nonempty_inter_compact hψ
  set s := hfin.toFinset with hs_def

  have hρ_smooth : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (ρ i : E → ℝ) := by
    intro i; rw [← contMDiff_iff_contDiff]; exact (ρ i).contMDiff

  have hprod_cs : ∀ i, HasCompactSupport (fun x => (↑(ρ i x) : ℂ) * ψ x) :=
    fun i => hψ.mul_left
  have hprod_smooth : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (↑(ρ i x) : ℂ) * ψ x) :=
    fun i => (Complex.ofRealCLM.contDiff.comp (hρ_smooth i)).mul (ψ.smooth ⊤)

  let g : E → 𝓢(E, ℂ) := fun i => (hprod_cs i).toSchwartzMap (hprod_smooth i)

  have hg_tsupport : ∀ i, tsupport (⇑(g i)) ⊆ S i := by
    intro i
    have heq : ∀ x, (g i) x = (↑(ρ i x) : ℂ) * ψ x :=
      (hprod_cs i).toSchwartzMap_toFun (hprod_smooth i)
    calc tsupport ⇑(g i) ⊆ tsupport (ρ i : E → ℝ) := by
            apply closure_mono
            intro x hx
            rw [Function.mem_support] at hx ⊢
            intro hρx; apply hx; simp [heq, hρx]
         _ ⊆ S i := hρ_sub i
  have hg_vanish : ∀ i, u (g i) = 0 :=
    fun i => hS_van i (g i) (hg_tsupport i)

  have hψ_eq : ψ = ∑ i ∈ s, g i := by
    ext x
    have hsum_app : (∑ i ∈ s, g i) x = ∑ i ∈ s, (g i) x := by
      change (⇑(∑ i ∈ s, g i)) x = _
      simp
    rw [hsum_app]
    have heq : ∀ i, (g i) x = (↑(ρ i x) : ℂ) * ψ x :=
      fun i => (hprod_cs i).toSchwartzMap_toFun (hprod_smooth i) x
    simp_rw [heq, ← Finset.sum_mul]


    by_cases hψx : ψ x = 0
    · simp [hψx]
    ·
      have hx_supp : x ∈ tsupport (⇑ψ) := subset_tsupport _ (Function.mem_support.mpr hψx)

      have hρ_zero : ∀ i, i ∉ s → (ρ i) x = 0 := by
        intro i hi
        by_contra h
        exact hi (hs_def ▸ hfin.mem_toFinset.mpr ⟨x, Function.mem_support.mpr h, hx_supp⟩)

      have hsum_one : ∑ᶠ i, (ρ i) x = 1 := ρ.sum_eq_one (Set.mem_univ x)

      have hsupp : Function.support (fun i => (ρ i) x) ⊆ ↑s := by
        intro i hi
        rw [Finset.mem_coe]
        by_contra hi'
        exact (Function.mem_support.mp hi) (hρ_zero i hi')

      rw [finsum_eq_sum_of_support_subset _ hsupp] at hsum_one


      have hcsum : (∑ i ∈ s, (↑(ρ i x) : ℂ)) = 1 := by
        rw [← Complex.ofReal_one, ← hsum_one]
        simp
      rw [hcsum, one_mul]

  rw [hψ_eq, map_sum]
  exact Finset.sum_eq_zero (fun i _ => hg_vanish i)

end TemperedDistribution

end
