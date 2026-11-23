/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation

set_option synthInstance.maxHeartbeats 80000

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable (𝔭 : HeightOneSpectrum A)

noncomputable def completionResidueMap :
    A →+* (𝔭.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) :=
  (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K))).comp
    (algebraMap A (𝔭.adicCompletionIntegers K))

theorem ker_completionResidueMap :
    RingHom.ker (𝔭.completionResidueMap (K := K)) = 𝔭.asIdeal := by
  ext a
  simp only [RingHom.mem_ker, completionResidueMap, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]

  have hval : Valued.v (↑(algebraMap A (𝔭.adicCompletionIntegers K) a) :
      𝔭.adicCompletion K) = 𝔭.valuation K (algebraMap A K a) := by
    simp only [algebraMap_adicCompletionIntegers_apply]
    exact valuedAdicCompletion_eq_valuation' 𝔭 (algebraMap A K a)
  have hle : Valued.v (↑(algebraMap A (𝔭.adicCompletionIntegers K) a) :
      𝔭.adicCompletion K) ≤ 1 :=
    (algebraMap A (𝔭.adicCompletionIntegers K) a).2
  rw [hval] at hle ⊢
  rw [← valuation_lt_one_iff_mem (K := K)]
  exact ⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩

lemma exists_mul_sub_mem_of_not_mem (b : A) (hb : b ∉ 𝔭.asIdeal) :
    ∃ e : A, b * e - 1 ∈ 𝔭.asIdeal := by
  haveI hmax : 𝔭.asIdeal.IsMaximal := 𝔭.isPrime.isMaximal 𝔭.ne_bot
  have hfield := (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔭.asIdeal).mp hmax
  have hne : Ideal.Quotient.mk 𝔭.asIdeal b ≠ 0 := by
    rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨inv, hinv⟩ := hfield.mul_inv_cancel hne
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective inv
  exact ⟨e, by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, sub_eq_zero]; exact hinv⟩

theorem surj_completionResidueMap :
    Function.Surjective (𝔭.completionResidueMap (K := K)) := by
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q

  have hd := 𝔭.denseRange_algebraMap K
  have hxcl := hd (x : 𝔭.adicCompletion K)
  rw [mem_closure_iff_nhds] at hxcl
  have hball : {y : 𝔭.adicCompletion K | Valued.v (y - ↑x) < 1} ∈ nhds (↑x) := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy => ?_⟩
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [Valued.v.restrict_lt_iff_lt_embedding] at hy
    simp only [Units.val_one, map_one] at hy
    exact hy
  obtain ⟨y, hy, ⟨k, rfl⟩⟩ := hxcl _ hball
  simp only [Set.mem_setOf_eq] at hy

  have hxle : Valued.v (x : 𝔭.adicCompletion K) ≤ 1 := x.2
  have hkle : Valued.v (algebraMap K (𝔭.adicCompletion K) k) ≤ 1 := by
    have : algebraMap K (𝔭.adicCompletion K) k =
        (x : 𝔭.adicCompletion K) -
          ((x : 𝔭.adicCompletion K) - algebraMap K (𝔭.adicCompletion K) k) := by ring
    rw [this]
    exact le_trans (Valued.v.map_sub _ _)
      (max_le hxle (le_of_lt (by rwa [Valuation.map_sub_swap] at hy)))
  have hkval : 𝔭.valuation K k ≤ 1 := by
    rwa [show Valued.v (algebraMap K (𝔭.adicCompletion K) k) = 𝔭.valuation K k from by
      erw [Valued.valuedCompletion_apply]; rfl] at hkle

  obtain ⟨a, ⟨b, hb⟩, hkab⟩ := 𝔭.exists_primeCompl_mul_eq_of_integer k hkval


  obtain ⟨t, hbt⟩ := 𝔭.exists_mul_sub_mem_of_not_mem b hb

  use a * t
  show completionResidueMap 𝔭 (a * t) = Ideal.Quotient.mk _ x
  simp only [completionResidueMap, RingHom.comp_apply]
  rw [Ideal.Quotient.eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      adicCompletionIntegers.isUnit_iff_valued_eq_one]
  suffices h : Valued.v (↑(algebraMap A (𝔭.adicCompletionIntegers K) (a * t) - x) :
      𝔭.adicCompletion K) < 1 from ne_of_lt h
  show Valued.v ((↑(algebraMap A (𝔭.adicCompletionIntegers K) (a * t)) : 𝔭.adicCompletion K) -
    (↑x : 𝔭.adicCompletion K)) < 1
  have hcoe_alg : (↑(algebraMap A (𝔭.adicCompletionIntegers K) (a * t)) : 𝔭.adicCompletion K) =
      algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t)) := by
    simp only [algebraMap_adicCompletionIntegers_apply, algebraMap_adicCompletion,
      Function.comp_apply]
    congr 1
  rw [hcoe_alg]

  have hterm1 : Valued.v (algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t)) -
      algebraMap K (𝔭.adicCompletion K) k) < 1 := by
    have halg_eq : algebraMap A K (a * t) - k = k * algebraMap A K (b * t - 1) := by
      simp only [map_mul, map_sub, map_one]
      rw [show algebraMap A K a = k * algebraMap A K b from hkab.symm]; ring
    have hval_bound : 𝔭.valuation K (algebraMap A K (a * t) - k) < 1 := by
      rw [halg_eq, map_mul]
      calc 𝔭.valuation K k * 𝔭.valuation K (algebraMap A K (b * t - 1))
          ≤ 1 * 𝔭.valuation K (algebraMap A K (b * t - 1)) :=
            mul_le_mul_left hkval _
          _ = 𝔭.valuation K (algebraMap A K (b * t - 1)) := one_mul _
          _ < 1 := (𝔭.valuation_lt_one_iff_mem (K := K) _).mpr hbt
    rw [show algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t)) -
        algebraMap K (𝔭.adicCompletion K) k =
        algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t) - k) from by rw [map_sub]]
    rw [show Valued.v (algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t) - k)) =
        𝔭.valuation K (algebraMap A K (a * t) - k) from by
      erw [Valued.valuedCompletion_apply]; rfl]
    exact hval_bound

  have hsplit : algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t)) - ↑x =
    (algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t)) -
      algebraMap K (𝔭.adicCompletion K) k) +
    (algebraMap K (𝔭.adicCompletion K) k - ↑x) := by ring
  rw [hsplit]
  exact lt_of_le_of_lt (Valued.v.map_add_le_max' _ _) (max_lt hterm1 hy)

end IsDedekindDomain.HeightOneSpectrum
