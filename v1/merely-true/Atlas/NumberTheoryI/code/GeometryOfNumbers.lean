/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.NumberTheoryI.code.DirichletSeries

universe u

noncomputable section

open MeasureTheory Measure Set Submodule ZLattice Module
open scoped NumberField

namespace GeometryOfNumbers

abbrev IsCocompactAddSubgroup {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    (H : AddSubgroup G) : Prop :=
  CompactSpace (G ⧸ H)


abbrev IsFullLattice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] : Prop :=
  IsZLattice ℝ L

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem discrete_full_rank_iff_zlattice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    finrank ℤ L = finrank ℝ E ↔ IsZLattice ℝ L := by
  constructor
  · intro h
    constructor

    let W := span ℝ (L : Set E)
    let f := W.subtype
    let L₀ : Submodule ℤ W := L.comap (f.restrictScalars ℤ)
    have h_img : f '' L₀ = L := by
      rw [← LinearMap.coe_restrictScalars ℤ f, ← Submodule.map_coe (f.restrictScalars ℤ),
        Submodule.map_comap_eq_self]
      exact fun x hx ↦ LinearMap.mem_range.mpr ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩
    have : DiscreteTopology L₀ := by
      refine DiscreteTopology.preimage_of_continuous_injective (L : Set E) ?_ (injective_subtype _)
      exact LinearMap.continuous_of_finiteDimensional f
    have : IsZLattice ℝ L₀ := ⟨by
      rw [← (Submodule.map_injective_of_injective (injective_subtype _)).eq_iff, Submodule.map_span,
        Submodule.map_top, range_subtype, h_img]⟩
    have h_surj : L₀.map (f.restrictScalars ℤ) = L := by
      rw [Submodule.map_comap_eq_self]
      exact fun x hx ↦ LinearMap.mem_range.mpr ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩
    have equiv : L₀ ≃ₗ[ℤ] L :=
      (L₀.equivMapOfInjective (f.restrictScalars ℤ) Subtype.val_injective).trans
        (LinearEquiv.ofEq _ _ h_surj)
    exact Submodule.eq_top_of_finrank_eq (by linarith [equiv.finrank_eq, ZLattice.rank ℝ L₀])
  · intro h
    haveI := h
    exact ZLattice.rank ℝ L


theorem measure_image_linearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (T : E →ₗ[ℝ] E) (S : Set E) :
    μ (T '' S) = ENNReal.ofReal |LinearMap.det T| * μ S :=
  μ.addHaar_image_linearMap T S


abbrev IsFundamentalDomain {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (L : Submodule ℤ E) (F : Set E)
    (μ : MeasureTheory.Measure E := by volume_tac) : Prop :=
  IsAddFundamentalDomain L F μ


theorem fundamental_domain_measure_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : MeasureTheory.Measure E := by volume_tac) [μ.IsAddHaarMeasure]
    {F : Set E} (hF : IsAddFundamentalDomain L F μ) :
    covolume L μ = μ.real F :=
  covolume_eq_measure_fundamentalDomain L μ hF


abbrev covol {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (L : Submodule ℤ E) (μ : MeasureTheory.Measure E := by volume_tac) : ℝ :=
  covolume L μ


theorem covol_sublattice {ι : Type*} [Fintype ι]
    (Λ' Λ : Submodule ℤ (ι → ℝ))
    [DiscreteTopology Λ'] [IsZLattice ℝ Λ']
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (h : Λ' ≤ Λ) :
    covolume Λ' = (Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) * covolume Λ := by
  have hcovol : covolume Λ ≠ 0 := covolume_ne_zero Λ volume
  rw [← covolume_div_covolume_eq_relIndex Λ' Λ h]
  field_simp


def IsSymmetricSet {V : Type*} [AddCommGroup V] (S : Set V) : Prop :=
  -S = S

theorem minkowski_lattice_point
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    {L : AddSubgroup E} [Countable L]
    {F : Set E} (hF : IsAddFundamentalDomain L F μ)
    {S : Set E}
    (h_symm : ∀ x ∈ S, -x ∈ S)
    (h_conv : Convex ℝ S)
    (h_meas : μ F * 2 ^ finrank ℝ E < μ S) :
    ∃ x ≠ 0, ((x : L) : E) ∈ S :=
  exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF h_symm h_conv h_meas


open NumberField.InfinitePlace NumberField.mixedEmbedding in
alias covol_ring_of_integers := covolume_integerLattice


open NumberField.InfinitePlace NumberField.mixedEmbedding in
alias covol_fractional_ideal := covolume_idealLattice


open NumberField.InfinitePlace in
open scoped nonZeroDivisors Real in
theorem minkowski_bound (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧
      |Algebra.norm ℚ (a : K)| ≤
        FractionalIdeal.absNorm I.1 * (4 / π) ^ nrComplexPlaces K *
          (finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) *
            Real.sqrt |↑(NumberField.discr K)| :=
  NumberField.exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K I


abbrev convexBody (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    Set (NumberField.mixedEmbedding.mixedSpace K) :=
  NumberField.mixedEmbedding.convexBodySum K t

open NumberField.InfinitePlace NumberField.mixedEmbedding in
alias convex_body_volume := convexBodySum_volume


open NumberField.InfinitePlace Ideal in
open scoped nonZeroDivisors Real in


open scoped nonZeroDivisors in

lemma finite_ideals_bounded_norm (K : Type*) [Field K] [NumberField K] (M : ℕ) :
    Set.Finite {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} :=
  (Ideal.finite_setOf_absNorm_le M).subset fun _ h => h.2

open UniqueFactorizationMonoid in
theorem normalizedFactors_card_le_log (K : Type*) [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (M : ℕ)
    (hIM : Ideal.absNorm I ≤ M) :
    (normalizedFactors I).card ≤ Nat.log 2 M := by
  apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
  calc 2 ^ (normalizedFactors I).card
      = 2 ^ ((normalizedFactors I).map (Ideal.absNorm : Ideal (𝓞 K) → ℕ)).card := by
          congr 1; exact (Multiset.card_map _ _).symm
    _ ≤ ((normalizedFactors I).map (Ideal.absNorm : Ideal (𝓞 K) → ℕ)).prod := by
          apply Multiset.pow_card_le_prod
          intro x hx
          rw [Multiset.mem_map] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          have hpbot : p ≠ ⊥ := ne_zero_of_mem_normalizedFactors hp
          have hpirr := irreducible_of_normalized_factor p hp
          have h1 : Ideal.absNorm p ≠ 0 := by rwa [ne_eq, Ideal.absNorm_eq_zero_iff]
          have h2 : Ideal.absNorm p ≠ 1 := by
            rw [ne_eq, Ideal.absNorm_eq_one_iff]
            exact fun h => hpirr.1 (Ideal.isUnit_iff.mpr h)
          omega
    _ = Ideal.absNorm I := by
          have h_prod := map_multiset_prod (Ideal.absNorm : Ideal (𝓞 K) →*₀ ℕ) (normalizedFactors I)
          have h_eq : (normalizedFactors I).prod = I :=
            associated_iff_eq.mp (prod_normalizedFactors (show I ≠ 0 from hI))
          rw [h_prod.symm, h_eq]
    _ ≤ M := hIM

open Ideal Finset in
set_option maxHeartbeats 400000 in

open UniqueFactorizationMonoid in
lemma prime_ideals_bounded_norm_card_lt (K : Type*) [Field K] [NumberField K] (M : ℕ)
    (hM : M ≠ 0) :
    Nat.card {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ Ideal.absNorm 𝔭 ≤ M} + 1 ≤
      finrank ℚ K * M := by
  by_cases hM1 : M = 1
  ·
    subst hM1
    have : Nat.card {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ Ideal.absNorm 𝔭 ≤ 1} = 0 := by
      rw [Nat.card_eq_zero]; left; rw [Set.isEmpty_coe_sort]; ext 𝔭
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h𝔭_prime h𝔭_ne h𝔭_norm
      have h1 : Ideal.absNorm 𝔭 ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr h𝔭_ne
      have h2 : Ideal.absNorm 𝔭 ≠ 1 := by
        rw [ne_eq, Ideal.absNorm_eq_one_iff]; exact h𝔭_prime.ne_top
      omega
    simp only [this, Nat.zero_add, mul_one]
    exact Module.finrank_pos
  ·
    have hM2 : 2 ≤ M := by omega
    classical

    open Ideal Finset in
    have hfin : Set.Finite {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ Ideal.absNorm 𝔭 ≤ M} := by
      apply Set.Finite.subset (Ideal.finite_setOf_absNorm_le M)
      intro I ⟨_, _, h⟩; exact h
    rw [Nat.card_eq_card_finite_toFinset hfin]
    set primes_le_M := (range (M + 1)).filter Nat.Prime with primes_le_M_def

    have hprimes_card : primes_le_M.card ≤ M - 1 := by
      have h : primes_le_M ⊆ (((range (M + 1)).erase 0).erase 1) := by
        intro x hx
        simp only [primes_le_M_def, Finset.mem_filter, Finset.mem_range] at hx
        simp only [Finset.mem_erase, Finset.mem_range]
        exact ⟨hx.2.ne_one, hx.2.ne_zero, hx.1⟩
      have h1 : (0 : ℕ) ∈ range (M + 1) := Finset.mem_range.mpr (by omega)
      have h2 : (1 : ℕ) ∈ (range (M + 1)).erase 0 := by
        simp [Finset.mem_erase, Finset.mem_range]; omega
      calc primes_le_M.card
          ≤ (((range (M + 1)).erase 0).erase 1).card := Finset.card_le_card h
        _ = ((range (M + 1)).erase 0).card - 1 := Finset.card_erase_of_mem h2
        _ ≤ (range (M + 1)).card - 1 - 1 := by rw [Finset.card_erase_of_mem h1]
        _ = M - 1 := by simp [Finset.card_range]


    set big_union := primes_le_M.biUnion
      (fun p => primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)) with big_union_def
    have h_sub : hfin.toFinset ⊆ big_union := by
      intro 𝔭 h𝔭
      rw [Set.Finite.mem_toFinset] at h𝔭
      obtain ⟨h𝔭_prime, h𝔭_ne, h𝔭_norm⟩ := h𝔭
      haveI : 𝔭.IsPrime := h𝔭_prime
      haveI : NeZero 𝔭 := ⟨h𝔭_ne⟩
      set p := Ideal.absNorm (Ideal.under ℤ 𝔭)
      have hp_prime : Nat.Prime p := Nat.absNorm_under_prime 𝔭
      have hp_le : p ≤ M :=
        le_trans (Nat.le_of_dvd (by rwa [Nat.pos_iff_ne_zero, ne_eq, absNorm_eq_zero_iff])
          (Int.absNorm_under_dvd_absNorm 𝔭)) h𝔭_norm
      rw [big_union_def, Finset.mem_biUnion]
      refine ⟨p, ?_, ?_⟩
      · simp only [primes_le_M_def, Finset.mem_filter, Finset.mem_range, hp_prime, and_true]; omega
      · have h_under_eq : Ideal.under ℤ 𝔭 = Ideal.span {(p : ℤ)} := by
          rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ 𝔭)]
        haveI : (Ideal.span {(p : ℤ)}).IsMaximal := by
          rw [← h_under_eq]; exact (h𝔭_prime.under ℤ).isMaximal (under_ne_bot ℤ h𝔭_ne)
        rw [mem_primesOverFinset_iff (by rw [← h_under_eq]; exact under_ne_bot ℤ h𝔭_ne)]
        exact ⟨h𝔭_prime, ⟨h_under_eq.symm⟩⟩
    calc hfin.toFinset.card + 1
        ≤ big_union.card + 1 := by linarith [Finset.card_le_card h_sub]
      _ ≤ (∑ p ∈ primes_le_M, (primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).card) + 1 := by
          have : big_union.card ≤ ∑ p ∈ primes_le_M,
            (primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).card := Finset.card_biUnion_le
          linarith
      _ ≤ (∑ _p ∈ primes_le_M, finrank ℚ K) + 1 := by
          have : ∑ p ∈ primes_le_M, (primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).card ≤
                 ∑ _p ∈ primes_le_M, finrank ℚ K := by
            apply Finset.sum_le_sum; intro p hp
            simp only [primes_le_M_def, Finset.mem_filter] at hp
            haveI : (Ideal.span {(p : ℤ)}).IsMaximal := by
              apply IsPrime.isMaximal
              · rw [Ideal.span_singleton_prime (Nat.cast_ne_zero.mpr hp.2.ne_zero)]
                exact Nat.prime_iff_prime_int.mp hp.2
              · rw [ne_eq, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.mpr hp.2.ne_zero
            exact card_primesOverFinset_le_finrank (𝓞 K) ℚ K
              (by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.mpr hp.2.ne_zero)
          linarith
      _ = primes_le_M.card * finrank ℚ K + 1 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (M - 1) * finrank ℚ K + 1 := by linarith [Nat.mul_le_mul_right (finrank ℚ K) hprimes_card]
      _ ≤ finrank ℚ K * M := by
          have hn : 0 < finrank ℚ K := Module.finrank_pos
          have hM1 : M = (M - 1) + 1 := by omega
          calc (M - 1) * finrank ℚ K + 1
              ≤ (M - 1) * finrank ℚ K + finrank ℚ K := by omega
            _ = ((M - 1) + 1) * finrank ℚ K := by ring
            _ = M * finrank ℚ K := by rw [← hM1]
            _ = finrank ℚ K * M := by ring

theorem ideals_bounded_norm_card_le (K : Type*) [Field K] [NumberField K] (M : ℕ) :
    Nat.card {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} ≤
      (finrank ℚ K * M) ^ Nat.log 2 M := by
  by_cases hM : M = 0
  ·
    subst hM
    convert Nat.zero_le _
    rw [Nat.card_eq_zero]
    left
    rw [Set.isEmpty_coe_sort]
    ext I
    simp only [Set.mem_setOf_eq, Nat.le_zero, Set.mem_empty_iff_false, iff_false, not_and]
    intro hne
    exact Ideal.absNorm_eq_zero_iff.not.mpr hne
  ·
    classical
    open UniqueFactorizationMonoid in
    set n := finrank ℚ K with hn_def
    set L := Nat.log 2 M with hL_def
    set P := n * M with hP_def

    set S := {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ Ideal.absNorm 𝔭 ≤ M}

    have hS_fin : Set.Finite S :=
      (Ideal.finite_setOf_absNorm_le M).subset (fun I ⟨_, _, h⟩ => h)
    haveI : Fintype S := hS_fin.fintype

    have hT_fin := finite_ideals_bounded_norm K M
    haveI : Finite {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} := hT_fin.to_subtype

    have factor_in_S : ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hIM : Ideal.absNorm I ≤ M)
        (p : Ideal (𝓞 K)) (hp : p ∈ normalizedFactors I), p ∈ S := by
      intro I hI hIM p hp
      refine ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor p hp),
             ne_zero_of_mem_normalizedFactors hp, ?_⟩
      exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero
        (Ideal.absNorm_eq_zero_iff.not.mpr hI))
        (map_dvd Ideal.absNorm (dvd_of_mem_normalizedFactors hp))) hIM

    have len_bound : ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hIM : Ideal.absNorm I ≤ M),
        (normalizedFactors I).toList.length ≤ L := by
      intro I hI hIM
      rw [Multiset.length_toList]
      exact normalizedFactors_card_le_log K I hI M hIM

    have all_in_S : ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hIM : Ideal.absNorm I ≤ M)
        (p : Ideal (𝓞 K)) (hp : p ∈ (normalizedFactors I).toList), p ∈ S :=
      fun I hI hIM p hp => factor_in_S I hI hIM p (Multiset.mem_toList.mp hp)

    let f : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} → (Fin L → Option S) :=
      fun ⟨I, hI_ne, hI_norm⟩ => fun i =>
        let list := (normalizedFactors I).toList
        if h : i.val < list.length then
          some ⟨list[i.val], all_in_S I hI_ne hI_norm _ (List.getElem_mem h)⟩
        else
          none

    have hf_inj : Function.Injective f := by
      intro ⟨I₁, hI₁_ne, hI₁_norm⟩ ⟨I₂, hI₂_ne, hI₂_norm⟩ hf_eq

      have hlen₁ := len_bound I₁ hI₁_ne hI₁_norm
      have hlen₂ := len_bound I₂ hI₂_ne hI₂_norm

      have hlen_eq : (normalizedFactors I₁).toList.length =
                     (normalizedFactors I₂).toList.length := by
        by_contra hne

        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        ·
          have h1 := congr_fun hf_eq ⟨(normalizedFactors I₁).toList.length, by omega⟩
          simp only [f, lt_irrefl, dite_false, hlt, dite_true] at h1
          exact nomatch h1
        ·
          have h1 := congr_fun hf_eq ⟨(normalizedFactors I₂).toList.length, by omega⟩
          simp only [f, hlt, dite_true, lt_irrefl, dite_false] at h1
          exact nomatch h1

      have toList_eq : (normalizedFactors I₁).toList = (normalizedFactors I₂).toList := by
        apply List.ext_getElem hlen_eq
        intro i hi₁ hi₂
        have h1 := congr_fun hf_eq ⟨i, by omega⟩
        simp only [f, show (i < (normalizedFactors I₁).toList.length) from hi₁,
                    show (i < (normalizedFactors I₂).toList.length) from hi₂,
                    dite_true] at h1
        have h2 := Option.some.inj h1
        exact congrArg Subtype.val h2

      have nf_eq : normalizedFactors I₁ = normalizedFactors I₂ := by
        have := congrArg Multiset.ofList toList_eq
        rwa [Multiset.coe_toList, Multiset.coe_toList] at this

      have : I₁ = I₂ := by
        have h1 := associated_iff_eq.mp (prod_normalizedFactors (show I₁ ≠ 0 from hI₁_ne))
        have h2 := associated_iff_eq.mp (prod_normalizedFactors (show I₂ ≠ 0 from hI₂_ne))
        rw [← h1, ← h2, nf_eq]
      exact Subtype.ext this

    have hS_strict : Nat.card S + 1 ≤ P := prime_ideals_bounded_norm_card_lt K M hM
    calc Nat.card {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ M}
        ≤ Nat.card (Fin L → Option S) := Nat.card_le_card_of_injective f hf_inj
      _ = (Nat.card S + 1) ^ L := by rw [Nat.card_fun, Finite.card_option, Nat.card_fin]
      _ ≤ P ^ L := by apply Nat.pow_le_pow_left; exact hS_strict
      _ = (finrank ℚ K * M) ^ Nat.log 2 M := by rfl


open scoped nonZeroDivisors in


theorem class_group_finite_integral_closure
    (A : Type*) [EuclideanDomain A] [Infinite A] [DecidableEq A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type*) [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    {abv : AbsoluteValue A ℤ} (adm : abv.IsAdmissible) :
    Finite (ClassGroup B) := by
  haveI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
  letI := ClassGroup.fintypeOfAdmissibleOfFinite K L adm (R := A) (S := B)
  infer_instance


open NumberField NumberField.InfinitePlace in
alias discr_lower_bound := abs_discr_ge'

open NumberField NumberField.InfinitePlace in


open NumberField NumberField.InfinitePlace in
theorem discr_abs_gt_one {K : Type*} [Field K] [NumberField K]
    (h : 1 < finrank ℚ K) : 1 < |discr K| :=
  lt_trans (by norm_num : (1 : ℤ) < 2) (abs_discr_gt_two h)


open NumberField in
alias finite_numberfields_of_bounded_discr := finite_of_discr_bdd




open Ideal NumberField UniqueFactorizationMonoid in
set_option maxHeartbeats 800000 in

theorem norm_valuation_discr_le (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    let 𝔭 : Ideal ℤ := Ideal.span {(p : ℤ)}
    emultiplicity (p : ℤ) (NumberField.discr K) ≤
      ↑(∑ P ∈ primesOverFinset 𝔭 (𝓞 K),
        Ideal.inertiaDeg 𝔭 P * (emultiplicity P (differentIdeal ℤ (𝓞 K))).toNat) := by
  intro 𝔭
  rw [← Int.emultiplicity_natAbs, ← NumberField.absNorm_differentIdeal K (𝓞 K)]
  set 𝒟 := differentIdeal ℤ (𝓞 K)
  have h𝒟_ne : 𝒟 ≠ ⊥ := differentIdeal_ne_bot
  have hprod : (normalizedFactors 𝒟).prod = 𝒟 := prod_normalizedFactors_eq_self h𝒟_ne
  conv_lhs => rw [← hprod]
  rw [show (normalizedFactors 𝒟).prod = (Multiset.map id (normalizedFactors 𝒟)).prod from by simp]
  rw [Finset.prod_multiset_map_count, map_prod (Ideal.absNorm : Ideal (𝓞 K) →*₀ ℕ)]
  simp_rw [id_eq, map_pow (Ideal.absNorm : Ideal (𝓞 K) →*₀ ℕ)]
  have hpp : Nat.Prime p := Fact.out
  rw [Finset.emultiplicity_prod hpp.prime]
  simp_rw [emultiplicity_pow hpp.prime]
  have hpne : (𝔭 : Ideal ℤ) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]; exact_mod_cast hpp.ne_zero
  haveI : 𝔭.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have key : ∀ x ∈ (normalizedFactors 𝒟).toFinset,
      ↑(Multiset.count x (normalizedFactors 𝒟)) * emultiplicity p (absNorm x) =
      if x ∈ primesOverFinset 𝔭 (𝓞 K) then
        ↑(𝔭.inertiaDeg x * (emultiplicity x 𝒟).toNat)
      else 0 := by
    intro x hx
    have hxirr : Irreducible x := irreducible_of_normalized_factor x (Multiset.mem_toFinset.mp hx)
    have hxne : x ≠ ⊥ := by intro h; rw [h] at hxirr; exact not_irreducible_zero hxirr
    have hxIsPrime : x.IsPrime :=
      Ideal.isPrime_of_prime (irreducible_iff_prime.mp hxirr)
    split_ifs with hxin
    ·
      have hxmem := (mem_primesOverFinset_iff hpne (𝓞 K)).mp hxin
      haveI : x.LiesOver 𝔭 := hxmem.2
      rw [Ideal.absNorm_eq_pow_inertiaDeg' x hpp, hpp.emultiplicity_pow_self]
      have hcount : Multiset.count x (normalizedFactors 𝒟) = (emultiplicity x 𝒟).toNat := by
        have h := emultiplicity_eq_count_normalizedFactors hxirr h𝒟_ne
        rw [normalize_eq] at h; rw [h]; simp
      rw [hcount]; push_cast; ring
    ·
      haveI := hxIsPrime
      have hunder_ne : x.under ℤ ≠ ⊥ := Ideal.under_ne_bot ℤ hxne
      rcases Ideal.isPrime_int_iff.mp (Ideal.IsPrime.under ℤ x) with h | ⟨q, hqprime, hq⟩
      · exact absurd h hunder_ne
      haveI : x.LiesOver (Ideal.span {(q : ℤ)}) :=
        ⟨by rw [Ideal.under_def] at hq; exact hq.symm⟩
      rw [Ideal.absNorm_eq_pow_inertiaDeg' x hqprime, emultiplicity_eq_zero.mpr (by
        intro h_dvd
        have hqne : q ≠ p := by
          intro heq; apply hxin
          rw [mem_primesOverFinset_iff hpne]
          refine ⟨hxIsPrime, ?_⟩
          have : Ideal.span {(q : ℤ)} = 𝔭 := by rw [heq]
          rwa [← this]

        exact hqne (by
          rcases hqprime.eq_one_or_self_of_dvd p (hpp.dvd_of_dvd_pow h_dvd) with h1 | h2
          · exact absurd h1 hpp.one_lt.ne'
          · exact h2.symm))]
      simp
  rw [Finset.sum_congr rfl key, ← Finset.sum_filter]
  calc ∑ x ∈ (normalizedFactors 𝒟).toFinset.filter (· ∈ primesOverFinset 𝔭 (𝓞 K)),
        (↑(𝔭.inertiaDeg x * (emultiplicity x 𝒟).toNat) : ℕ∞)
      ≤ ∑ x ∈ primesOverFinset 𝔭 (𝓞 K),
        (↑(𝔭.inertiaDeg x * (emultiplicity x 𝒟).toNat) : ℕ∞) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => (Finset.mem_filter.mp hx).2) (by intros; exact bot_le)
    _ = ↑(∑ x ∈ primesOverFinset 𝔭 (𝓞 K), 𝔭.inertiaDeg x * (emultiplicity x 𝒟).toNat) := by
        rw [Nat.cast_sum]



theorem emultiplicity_span_natCast_eq (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K))
    (hP : P ∈ primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K))
    (n : ℕ) (hn : n ≠ 0) :
    let 𝔭 : Ideal ℤ := Ideal.span {(p : ℤ)}
    emultiplicity P (Ideal.span {(n : 𝓞 K)}) =
      ↑(Ideal.ramificationIdx 𝔭 P * padicValNat p n) := by
  intro 𝔭

  simp only [primesOverFinset, Multiset.mem_toFinset] at hP
  have hPprime := UniqueFactorizationMonoid.prime_of_factor P hP
  haveI : P.IsPrime := Ideal.isPrime_of_prime hPprime
  have hPne : P ≠ ⊥ := hPprime.ne_zero
  have hPirr : Irreducible P := UniqueFactorizationMonoid.irreducible_of_factor P hP

  have hp_prime : Nat.Prime p := Fact.out
  have hp_ne_zero : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp_prime.ne_zero
  have h𝔭_ne : 𝔭 ≠ ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
  have h𝔭_prime : 𝔭.IsPrime := by
    show (Ideal.span {(p : ℤ)}).IsPrime
    rw [Ideal.span_singleton_prime hp_ne_zero]
    exact Nat.prime_iff_prime_int.mp hp_prime
  have h𝔭_irr : Irreducible 𝔭 := (Ideal.prime_of_isPrime h𝔭_ne h𝔭_prime).irreducible

  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal ‹P.IsPrime› hPne
  haveI : 𝔭.IsMaximal := h𝔭_prime.isMaximal (by rwa [ne_eq, Ideal.span_singleton_eq_bot])
  haveI : P.LiesOver 𝔭 := by
    constructor
    show 𝔭 = Ideal.comap (algebraMap ℤ (𝓞 K)) P
    have hdvd := UniqueFactorizationMonoid.dvd_of_mem_factors hP
    rw [Ideal.dvd_iff_le] at hdvd
    apply Ideal.IsMaximal.eq_of_le ‹𝔭.IsMaximal›
    · intro h
      have h1 : (1 : 𝓞 K) ∈ P := by
        have h2 := (Ideal.eq_top_iff_one _).mp h
        rwa [Ideal.mem_comap, map_one] at h2
      exact Ideal.IsPrime.ne_top ‹P.IsPrime› ((Ideal.eq_top_iff_one _).mpr h1)
    · exact le_trans Ideal.le_comap_map (Ideal.comap_mono hdvd)

  have hspan : Ideal.span {(n : 𝓞 K)} =
      Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(n : ℤ)}) := by
    rw [Ideal.map_span]
    congr 1
    simp [Set.image_singleton]
  rw [hspan]

  have hI_ne : (Ideal.span {(n : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
  rw [Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul hI_ne h𝔭_irr hPirr hPne]

  rw [show 𝔭 = Ideal.span {(p : ℤ)} from rfl, emultiplicity_eq_emultiplicity_span]
  rw [Int.natCast_emultiplicity, ← padicValNat_eq_emultiplicity (hn := hn)]
  simp [Nat.cast_mul]



lemma sum_reindex_fin {α : Type*} {β : Type*} [AddCommMonoid β] (S : Finset α) (g : α → β) :
    ∑ x ∈ S, g x = ∑ i : Fin S.card, g (S.equivFin.symm i) := by
  conv_lhs => rw [← Finset.sum_attach S]
  exact Finset.sum_equiv S.equivFin (fun i => by simp)
    (fun i _ => by simp [Equiv.symm_apply_apply])


lemma sum_ramification_padic_le {ι : Type*} (S : Finset ι) (e f : ι → ℕ) (p n : ℕ)
    (he : ∀ i ∈ S, 1 ≤ e i) (hf : ∀ i ∈ S, 1 ≤ f i) (hS : S.Nonempty)
    (hsum : ∑ i ∈ S, e i * f i = n) :
    ∑ i ∈ S, f i * (e i - 1 + e i * padicValNat p (e i)) ≤ n * Nat.log p n + n - 1 := by
  set L := ∑ i ∈ S, f i * (e i - 1 + e i * padicValNat p (e i))
  set Sf := ∑ i ∈ S, f i
  set Sv := ∑ i ∈ S, f i * (e i * padicValNat p (e i))

  have hident : L + Sf = n + Sv := by
    simp only [L, Sf, Sv]
    rw [← Finset.sum_add_distrib, ← hsum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    nlinarith [Nat.sub_add_cancel (he i hi)]

  have hSv : Sv ≤ n * Nat.log p n := by
    simp only [Sv]
    calc ∑ i ∈ S, f i * (e i * padicValNat p (e i))
        ≤ ∑ i ∈ S, f i * (e i * Nat.log p n) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Nat.mul_le_mul_left
          apply Nat.mul_le_mul_left
          calc padicValNat p (e i) ≤ Nat.log p (e i) := padicValNat_le_nat_log _
            _ ≤ Nat.log p n := Nat.log_mono_right (by
                calc e i ≤ e i * f i := Nat.le_mul_of_pos_right _ (hf i hi)
                  _ ≤ ∑ j ∈ S, e j * f j :=
                      Finset.single_le_sum (f := fun j => e j * f j)
                        (fun j _ => Nat.zero_le _) hi
                  _ = n := hsum)
      _ = (∑ i ∈ S, e i * f i) * Nat.log p n := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _; ring
      _ = n * Nat.log p n := by rw [hsum]

  have hSf : 1 ≤ Sf := by
    simp only [Sf]
    obtain ⟨i, hi⟩ := hS
    calc 1 ≤ f i := hf i hi
      _ ≤ ∑ j ∈ S, f j :=
          Finset.single_le_sum (f := fun i => f i) (fun j _ => Nat.zero_le _) hi

  omega


open NumberField in


open Polynomial in


open NumberField in
def IsUnramifiedOutside (K : Type*) [Field K] [NumberField K] (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S → ¬((p : ℤ) ∣ discr K)


lemma isUnramifiedOutside_filter_prime {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} :
    IsUnramifiedOutside K S ↔ IsUnramifiedOutside K (S.filter Nat.Prime) := by
  constructor
  · intro h p hp hnotin
    exact h p hp (fun hin => hnotin (Finset.mem_filter.mpr ⟨hin, hp⟩))
  · intro h p hp hnotin
    exact h p hp (fun hin => hnotin ((Finset.mem_filter.mp hin).1))





open Ideal in


open NumberField NumberField.InfinitePlace in

open NumberField NumberField.InfinitePlace in

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding in
open scoped nonZeroDivisors NNReal Classical in

theorem arakelov_minkowski_bound (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {f : InfinitePlace K → ℝ≥0}
    (hc : minkowskiBound K I < volume (convexBodyLT K f)) :
    ∃ a ∈ (↑I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧
      ∀ w : InfinitePlace K, w a ≤ f w := by
  obtain ⟨a, ha_mem, ha_ne, ha_bd⟩ := exists_ne_zero_mem_ideal_lt K I hc
  exact ⟨a, ha_mem, ha_ne, fun w => le_of_lt (ha_bd w)⟩

end GeometryOfNumbers
