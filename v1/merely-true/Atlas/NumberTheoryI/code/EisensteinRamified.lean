/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.FieldTheory.Separable
import Atlas.NumberTheoryI.code.LocalExtensions

open Polynomial Ideal IsLocalRing

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

namespace Polynomial

abbrev IsEisenstein (f : A[X]) : Prop :=
  f.IsEisensteinAt (IsLocalRing.maximalIdeal A)

theorem IsEisenstein.irreducible_in_ring {f : A[X]}
    (heis : f.IsEisenstein) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Irreducible f :=
  heis.irreducible (IsLocalRing.maximalIdeal.isMaximal A).isPrime hf.isPrimitive hdeg

theorem IsEisenstein.irreducible_map_fractionField {f : A[X]}
    (heis : f.IsEisenstein) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K] :
    Irreducible (f.map (algebraMap A K)) :=
  (hf.irreducible_iff_irreducible_map_fraction_map).mp
    (heis.irreducible_in_ring hf hdeg)

end Polynomial

section EisensteinAdjoinRoot

variable {A : Type*} [CommRing A]

lemma coeff0_image_mem_span_root (f : A[X]) :
    algebraMap A (AdjoinRoot f) (f.coeff 0) ∈ Ideal.span {AdjoinRoot.root f} := by
  have heval := AdjoinRoot.eval₂_root f
  rw [Polynomial.eval₂_eq_sum_range] at heval
  rw [Finset.sum_range_succ'] at heval
  simp only [pow_zero, mul_one] at heval
  rw [add_comm] at heval
  have hcoeff0 := eq_neg_of_add_eq_zero_left heval
  change AdjoinRoot.of f (f.coeff 0) ∈ _
  rw [hcoeff0]
  apply neg_mem
  apply Ideal.sum_mem
  intro i _
  apply Ideal.mul_mem_left
  rw [pow_succ']
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

variable [IsDomain A] [IsDiscreteValuationRing A]

lemma maximalIdeal_eq_span_coeff0 (f : A[X])
    (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
    (hdeg : 0 < f.natDegree) :
    IsLocalRing.maximalIdeal A = Ideal.span {f.coeff 0} := by
  have ha_mem : f.coeff 0 ∈ IsLocalRing.maximalIdeal A := heis.mem (by omega)
  have ha_notmem : f.coeff 0 ∉ (IsLocalRing.maximalIdeal A) ^ 2 := heis.notMem
  have ha_ne : f.coeff 0 ≠ 0 := fun h => ha_notmem (h ▸ Ideal.zero_mem _)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, u, heq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha_ne hϖ
  rw [hϖ.maximalIdeal_eq] at ha_mem ha_notmem
  rw [Ideal.span_singleton_pow] at ha_notmem
  have hn_ge : 1 ≤ n := by
    by_contra h
    simp only [not_le, Nat.lt_one_iff] at h
    subst h; simp only [pow_zero, mul_one] at heq
    rw [heq, Ideal.mem_span_singleton] at ha_mem
    exact hϖ.not_isUnit (isUnit_of_dvd_unit ha_mem u.isUnit)
  have hn_le : n ≤ 1 := by
    by_contra h
    simp only [not_le] at h
    apply ha_notmem; rw [heq, Ideal.mem_span_singleton]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    exact ⟨↑u * ϖ ^ k, by ring⟩
  have hn1 : n = 1 := le_antisymm hn_le hn_ge
  subst hn1
  simp only [pow_one] at heq ha_mem ha_notmem ⊢
  rw [heq]
  exact (Associated.irreducible ⟨u, mul_comm ϖ ↑u⟩ hϖ).maximalIdeal_eq

lemma map_maxIdeal_le_span_root (f : A[X])
    (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
    (hdeg : 0 < f.natDegree) :
    Ideal.map (algebraMap A (AdjoinRoot f)) (IsLocalRing.maximalIdeal A) ≤
      Ideal.span {AdjoinRoot.root f} := by
  rw [maximalIdeal_eq_span_coeff0 f heis hdeg, Ideal.map_span, Set.image_singleton]
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact coeff0_image_mem_span_root f

lemma adjoinRoot_root_ne_zero (f : A[X])
    (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    AdjoinRoot.root f ≠ 0 := by
  show (AdjoinRoot.mk f) X ≠ 0
  intro h
  rw [AdjoinRoot.mk_eq_zero] at h
  obtain ⟨g, hg⟩ := h

  have h0 : 0 = f.coeff 0 * g.coeff 0 := by
    have := congr_arg (fun p => p.coeff 0) hg
    simp only [coeff_X_zero, mul_coeff_zero] at this
    exact this
  have ha_ne : f.coeff 0 ≠ 0 := fun h => heis.notMem (h ▸ Ideal.zero_mem _)

  have hg0 : g.coeff 0 = 0 := by
    rcases mul_eq_zero.mp h0.symm with h | h
    · exact absurd h ha_ne
    · exact h

  have hf_ne : f ≠ 0 := hf.ne_zero
  have hg_ne : g ≠ 0 := right_ne_zero_of_mul (hg ▸ X_ne_zero)
  have hdeg_eq : 1 = natDegree f + natDegree g := by
    rw [← natDegree_X (R := A), hg, natDegree_mul hf_ne hg_ne]
  have hnd_g : natDegree g = 0 := by omega

  rw [eq_C_of_natDegree_eq_zero hnd_g] at hg0
  simp only [coeff_C_zero] at hg0
  rw [eq_C_of_natDegree_eq_zero hnd_g, hg0, map_zero] at hg_ne
  exact hg_ne rfl

theorem adjoinRoot_eisenstein_isDVR (f : A[X])
    (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
    (hf : f.Monic) (hdeg : 0 < f.natDegree)
    [h_local : IsLocalRing (AdjoinRoot f)]
    (h_maxeq_cor : IsLocalRing.maximalIdeal (AdjoinRoot f) =
      Ideal.map (algebraMap A (AdjoinRoot f)) (IsLocalRing.maximalIdeal A) ⊔
      Ideal.span {AdjoinRoot.root f}) :
    @IsDiscreteValuationRing (AdjoinRoot f) _
      (AdjoinRoot.isDomain_of_prime
        (UniqueFactorizationMonoid.irreducible_iff_prime.mp
          (heis.irreducible (maximalIdeal.isMaximal A).isPrime hf.isPrimitive hdeg))) := by

  haveI hdom : IsDomain (AdjoinRoot f) :=
    AdjoinRoot.isDomain_of_prime
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (heis.irreducible (maximalIdeal.isMaximal A).isPrime hf.isPrimitive hdeg))

  have h_maxeq : IsLocalRing.maximalIdeal (AdjoinRoot f) =
      Ideal.span {AdjoinRoot.root f} := by
    rw [h_maxeq_cor, sup_eq_right]
    exact map_maxIdeal_le_span_root f heis hdeg

  have h_principal : (IsLocalRing.maximalIdeal (AdjoinRoot f)).IsPrincipal :=
    ⟨⟨AdjoinRoot.root f, h_maxeq⟩⟩

  have h_not_field : ¬IsField (AdjoinRoot f) := by
    intro hfield
    have : IsLocalRing.maximalIdeal (AdjoinRoot f) = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    rw [h_maxeq, Ideal.span_singleton_eq_bot] at this
    exact adjoinRoot_root_ne_zero f heis hf hdeg this

  haveI : IsNoetherianRing (AdjoinRoot f) := AdjoinRoot.instIsNoetherianRing

  exact ((IsDiscreteValuationRing.TFAE (AdjoinRoot f) h_not_field).out 4 0).mp h_principal

end EisensteinAdjoinRoot

section ResidueFieldSurjectivity

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B]

lemma residue_aeval_eq_residue_const (π : B) (hπ_mem : π ∈ IsLocalRing.maximalIdeal B)
    (p : A[X]) :
    (IsLocalRing.residue B) (Polynomial.aeval π p) =
    (IsLocalRing.residue B) (algebraMap A B (p.coeff 0)) := by
  simp only [Polynomial.aeval_def]
  rw [Polynomial.hom_eval₂]
  conv_lhs => rw [show (IsLocalRing.residue B) π = 0 from
    Ideal.Quotient.eq_zero_iff_mem.mpr hπ_mem]
  rw [Polynomial.eval₂_at_zero]; rfl

variable [IsLocalRing A] [IsLocalHom (algebraMap A B)]

lemma residueField_map_surj_of_adjoin_uniformizer (π : B) (hπ : Irreducible π)
    (hadj : Algebra.adjoin A ({π} : Set B) = ⊤) :
    Function.Surjective (IsLocalRing.ResidueField.map (algebraMap A B)) := by
  intro b
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hb₀ : b₀ ∈ Algebra.adjoin A ({π} : Set B) := by rw [hadj]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb₀
  obtain ⟨p, rfl⟩ := hb₀
  have hπ_mem : π ∈ IsLocalRing.maximalIdeal B := by
    rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π
  refine ⟨IsLocalRing.residue A (p.coeff 0), ?_⟩
  rw [IsLocalRing.ResidueField.map_residue]
  show (IsLocalRing.residue B) (algebraMap A B (p.coeff 0)) =
    (IsLocalRing.residue B) (Polynomial.aeval π p)
  exact (residue_aeval_eq_residue_const π hπ_mem p).symm

lemma finrank_eq_one_of_algebraMap_surjective {k l : Type*} [Field k] [Field l] [Algebra k l]
    (hsurj : Function.Surjective (algebraMap k l)) : Module.finrank k l = 1 := by
  have hbij : Function.Bijective (Algebra.ofId k l) :=
    ⟨(algebraMap k l).injective, hsurj⟩
  let e : k ≃ₐ[k] l := AlgEquiv.ofBijective (Algebra.ofId k l) hbij
  have h := LinearEquiv.finrank_eq e.symm.toLinearEquiv
  linarith [Module.finrank_self k]

end ResidueFieldSurjectivity

section TotalRamificationEisenstein

variable
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]

theorem eisenstein_implies_totally_ramified
    (π : B) (hπ : Irreducible π)
    (hadj : Algebra.adjoin A ({π} : Set B) = ⊤)
    (_heis : (minpoly A π).IsEisensteinAt (IsLocalRing.maximalIdeal A)) :
    (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
      Module.finrank K L := by


  have hsurj : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap A B)) :=
    residueField_map_surj_of_adjoin_uniformizer π hπ hadj


  have hf1 : AKLB_resDeg A B = 1 :=
    finrank_eq_one_of_algebraMap_surjective hsurj

  have hfund := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
  rw [hf1, mul_one] at hfund
  exact hfund.symm

theorem uniformizer_powers_span_mod_maximal
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (π : B) (hπ : Irreducible π)
    (htotram : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
      Module.finrank K L) :
    (⊤ : Submodule A B) ≤
      (Algebra.adjoin A ({π} : Set B)).toSubmodule ⊔ (IsLocalRing.maximalIdeal A) • ⊤ := by
  set S := Algebra.adjoin A ({π} : Set B)
  set n := Module.finrank K L
  set e := (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B)
  set f := AKLB_resDeg A B

  have he_eq_n : e = n := htotram
  have hefn : n = e * f := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
  have hf1 : f = 1 := by
    have hne : e ≠ 0 := by
      intro h; rw [h] at he_eq_n
      exact absurd he_eq_n.symm (Module.finrank_pos (R := K) (M := L)).ne'
    have hfe : e * f = e * 1 := by rw [mul_one]; linarith
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) hfe

  have hres_surj : Function.Surjective (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) := by
    have htop := Subalgebra.bot_eq_top_of_finrank_eq_one hf1
    intro x
    exact (htop ▸ Algebra.mem_top : x ∈ (⊥ : Subalgebra _ _))

  have hlift : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ IsLocalRing.maximalIdeal B := by
    intro b
    obtain ⟨abar, habar⟩ := hres_surj (IsLocalRing.residue B b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective abar
    exact ⟨a, (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      (show (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)) (algebraMap A B a) =
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)) b from by
        show (IsLocalRing.residue B) (algebraMap A B a) = (IsLocalRing.residue B) b
        rw [← IsLocalRing.ResidueField.map_residue (algebraMap A B) a]
        show (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
              ((IsLocalRing.residue A) a) = (IsLocalRing.residue B) b
        exact habar).symm⟩

  have hπ_span : IsLocalRing.maximalIdeal B = Ideal.span {π} := hπ.maximalIdeal_eq

  have span_pow_eq : ∀ k : ℕ, (IsLocalRing.maximalIdeal B) ^ k = Ideal.span {π ^ k} := by
    intro k; rw [hπ_span, Ideal.span_singleton_pow]

  have hind_step : ∀ k : ℕ, (((IsLocalRing.maximalIdeal B) ^ k).restrictScalars A : Submodule A B) ≤
      S.toSubmodule ⊔ ((IsLocalRing.maximalIdeal B) ^ (k + 1)).restrictScalars A := by
    intro k m hm
    simp only [Submodule.restrictScalars_mem] at hm
    rw [span_pow_eq k, Ideal.mem_span_singleton'] at hm
    obtain ⟨c, hc⟩ := hm
    obtain ⟨a, ha⟩ := hlift c
    have hmdecomp : m = algebraMap A B a * π ^ k + (c - algebraMap A B a) * π ^ k := by
      rw [← add_mul, add_sub_cancel, hc]
    rw [hmdecomp]
    apply Submodule.add_mem_sup
    · exact Subalgebra.mul_mem S (S.algebraMap_mem a)
        (Subalgebra.pow_mem S (Algebra.subset_adjoin (Set.mem_singleton π)) k)
    · show (c - algebraMap A B a) * π ^ k ∈
        ((IsLocalRing.maximalIdeal B) ^ (k + 1)).restrictScalars A
      simp only [Submodule.restrictScalars_mem]
      have hd : c - algebraMap A B a ∈ IsLocalRing.maximalIdeal B := ha
      have hpk : π ^ k ∈ (IsLocalRing.maximalIdeal B) ^ k := by
        rw [span_pow_eq k]; exact Ideal.mem_span_singleton_self _
      rw [pow_succ]
      exact mul_comm (c - algebraMap A B a) (π ^ k) ▸ Ideal.mul_mem_mul hpk hd

  have hiter : ∀ b : B,
      b ∈ S.toSubmodule ⊔ ((IsLocalRing.maximalIdeal B) ^ n).restrictScalars A := by
    intro b
    suffices h : ∀ k : ℕ, b ∈ S.toSubmodule ⊔
        ((IsLocalRing.maximalIdeal B) ^ k).restrictScalars A from h n
    intro k
    induction k with
    | zero =>
      have : b ∈ ((IsLocalRing.maximalIdeal B) ^ 0).restrictScalars A := by
        simp
      exact Submodule.mem_sup_right this
    | succ k ih =>
      have hle : S.toSubmodule ⊔ ((IsLocalRing.maximalIdeal B) ^ k).restrictScalars A ≤
          S.toSubmodule ⊔ ((IsLocalRing.maximalIdeal B) ^ (k + 1)).restrictScalars A :=
        (sup_le_sup_left (hind_step k) S.toSubmodule).trans
          (by rw [← sup_assoc, sup_idem])
      exact hle ih

  have hmap_eq : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      (IsLocalRing.maximalIdeal B) ^ e := by
    set I := Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)
    have hinj : Function.Injective (algebraMap A B) :=
      FaithfulSMul.algebraMap_injective A B
    have hIne : I ≠ ⊥ := by
      intro h
      have : IsLocalRing.maximalIdeal A = ⊥ := by
        rw [Ideal.map_eq_bot_iff_le_ker] at h
        have hker : RingHom.ker (algebraMap A B) = ⊥ :=
          (RingHom.injective_iff_ker_eq_bot _).mp hinj
        rw [hker] at h
        exact le_bot_iff.mp h
      exact IsDiscreteValuationRing.not_a_field A this
    obtain ⟨m, hm⟩ := exists_maximalIdeal_pow_eq_of_principal B
      (IsPrincipalIdealRing.principal _) I hIne
    have hgt : ¬(I ≤ (IsLocalRing.maximalIdeal B) ^ (m + 1)) := by
      intro hle
      have hle' : (IsLocalRing.maximalIdeal B) ^ m ≤ (IsLocalRing.maximalIdeal B) ^ (m + 1) :=
        hm ▸ hle
      have : (IsLocalRing.maximalIdeal B : Ideal B) ^ m = ⊥ := by
        have key : ((IsLocalRing.maximalIdeal B) ^ m : Ideal B) ≤
            IsLocalRing.maximalIdeal B • ((IsLocalRing.maximalIdeal B) ^ m : Ideal B) := by
          calc ((IsLocalRing.maximalIdeal B) ^ m : Ideal B)
              ≤ (IsLocalRing.maximalIdeal B) ^ (m + 1) := hle'
            _ = (IsLocalRing.maximalIdeal B) ^ m * IsLocalRing.maximalIdeal B := pow_succ _ m
            _ = IsLocalRing.maximalIdeal B * (IsLocalRing.maximalIdeal B) ^ m := mul_comm _ _
            _ = IsLocalRing.maximalIdeal B • (IsLocalRing.maximalIdeal B) ^ m :=
                (Ideal.smul_eq_mul _ _).symm
        exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
          (IsLocalRing.maximalIdeal B) ((IsLocalRing.maximalIdeal B) ^ m : Ideal B)
          (IsNoetherian.noetherian _) key
          (by rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top])
      exact hIne (hm.trans this)
    have hme : m = e := by
      have h1 : I ≤ (IsLocalRing.maximalIdeal B) ^ m := hm ▸ le_refl _
      exact (Ideal.ramificationIdx_spec h1 hgt).symm
    rw [← hme, hm]
  have hpow_le_smul : ((IsLocalRing.maximalIdeal B) ^ n).restrictScalars A ≤
      (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A B) := by
    rw [Ideal.smul_top_eq_map, ← he_eq_n, hmap_eq]

  intro b _
  have hb := hiter b
  exact (sup_le_sup_left hpow_le_smul S.toSubmodule) hb

theorem totally_ramified_adjoin_uniformizer
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (π : B) (hπ : Irreducible π)
    (htotram : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
      Module.finrank K L) :
    Algebra.adjoin A ({π} : Set B) = ⊤ := by


  exact subalgebra_eq_top_of_mod_maximal _ (uniformizer_powers_span_mod_maximal A K B L π hπ htotram)

theorem totally_ramified_minpoly_coeff_mem
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (π : B) (_hπ : Irreducible π)
    (_htotram : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
      Module.finrank K L)
    {n : ℕ} (_hn : n < (minpoly A π).natDegree) :
    (minpoly A π).coeff n ∈ IsLocalRing.maximalIdeal A := by
  set f := minpoly A π
  set 𝔭 := IsLocalRing.maximalIdeal A
  set 𝔪 := IsLocalRing.maximalIdeal B
  set d := f.natDegree
  set e := 𝔭.ramificationIdx 𝔪
  have hπ_int : IsIntegral A π := IsIntegral.of_finite A π
  have heval : ∑ i ∈ Finset.range (d + 1), (algebraMap A B) (f.coeff i) * π ^ i = 0 := by
    have h := minpoly.aeval A π
    rw [Polynomial.aeval_eq_sum_range] at h
    simp only [Algebra.smul_def] at h
    exact h
  have hπ_span : 𝔪 = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp _hπ
  have hπ_mem : π ∈ 𝔪 := hπ_span ▸ Ideal.mem_span_singleton_self π
  have hram : Ideal.map (algebraMap A B) 𝔭 ≤ 𝔪 ^ e := Ideal.le_pow_ramificationIdx
  have hde : d ≤ e := by
    rw [_htotram]
    calc d = ((minpoly A π).map (algebraMap A K)).natDegree := by
              rw [(minpoly.monic hπ_int).natDegree_map]
         _ = (minpoly K (algebraMap B L π)).natDegree := by
              rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hπ_int]
         _ ≤ Module.finrank K L := minpoly.natDegree_le (algebraMap B L π)
  suffices h_strong : ∀ k, k < d → f.coeff k ∈ 𝔭 by exact h_strong n _hn
  intro k hk
  induction k using Nat.strongRecOn with
  | _ k ih =>
  have hk_mem : k ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  have heval' := heval
  rw [← Finset.add_sum_erase _ _ hk_mem] at heval'
  have heq := eq_neg_of_add_eq_zero_left heval'
  have h_prod : (algebraMap A B) (f.coeff k) * π ^ k ∈ 𝔪 ^ (k + 1) := by
    rw [heq]
    apply Submodule.neg_mem
    apply Ideal.sum_mem
    intro i hi
    rw [Finset.mem_erase] at hi
    obtain ⟨hne, hi_range⟩ := hi
    rw [Finset.mem_range] at hi_range
    by_cases hlt : i < k
    · have hcoeff_mem : f.coeff i ∈ 𝔭 := ih i hlt (by omega)
      exact Ideal.pow_le_pow_right (by omega)
        (pow_add 𝔪 e i ▸ Ideal.mul_mem_mul (hram (Ideal.mem_map_of_mem _ hcoeff_mem))
          (Ideal.pow_mem_pow hπ_mem i))
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow hπ_mem i))
  have h_in_𝔪 : (algebraMap A B) (f.coeff k) ∈ 𝔪 := by
    rw [hπ_span, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h_prod
    rw [hπ_span, Ideal.mem_span_singleton]
    obtain ⟨c, hc⟩ := h_prod
    exact ⟨c, mul_right_cancel₀ (pow_ne_zero k _hπ.ne_zero) (by rw [hc]; ring)⟩
  rwa [IsLocalRing.mem_maximalIdeal, ← map_mem_nonunits_iff (algebraMap A B),
       ← IsLocalRing.mem_maximalIdeal]

theorem totally_ramified_coeff0_image_not_in_pow_succ
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (π : B) (_hπ : Irreducible π)
    (_htotram : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
      Module.finrank K L) :
    algebraMap A B ((minpoly A π).coeff 0) ∉
      (IsLocalRing.maximalIdeal B) ^ (Module.finrank K L + 1) := by
  set f := minpoly A π
  set 𝔭 := IsLocalRing.maximalIdeal A
  set 𝔮 := IsLocalRing.maximalIdeal B
  set n := Module.finrank K L
  set d := f.natDegree
  have hπ_int : IsIntegral A π := IsIntegral.of_finite A π

  have heval : ∑ i ∈ Finset.range (d + 1), (algebraMap A B) (f.coeff i) * π ^ i = 0 := by
    have h := minpoly.aeval A π
    rw [Polynomial.aeval_eq_sum_range] at h
    simp only [Algebra.smul_def] at h
    exact h

  have hπ_span : 𝔮 = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp _hπ
  have hπ_mem : π ∈ 𝔮 := hπ_span ▸ Ideal.mem_span_singleton_self π

  have hram : Ideal.map (algebraMap A B) 𝔭 ≤ 𝔮 ^ n := by
    have := @Ideal.le_pow_ramificationIdx A _ B _ _ 𝔭 𝔮
    rwa [_htotram] at this

  have hde : d ≤ n := by
    calc d = ((minpoly A π).map (algebraMap A K)).natDegree := by
              rw [(minpoly.monic hπ_int).natDegree_map]
         _ = (minpoly K (algebraMap B L π)).natDegree := by
              rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hπ_int]
         _ ≤ Module.finrank K L := minpoly.natDegree_le (algebraMap B L π)

  have hfmonic : f.Monic := minpoly.monic hπ_int
  have hcoeff_d : f.coeff d = 1 := hfmonic.leadingCoeff

  intro ha₀_mem

  have hπd_not : π ^ d ∉ 𝔮 ^ (d + 1) := by
    rw [hπ_span, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro ⟨c, hc⟩
    have hπd_ne : π ^ d ≠ 0 := pow_ne_zero d _hπ.ne_zero
    have hmul : π * c = 1 := by
      have h : π ^ d * (π * c) = π ^ d * 1 := by
        rw [← mul_assoc, ← pow_succ, hc, mul_one]
      exact mul_left_cancel₀ hπd_ne h
    exact _hπ.not_isUnit ⟨⟨π, c, hmul, mul_comm c π ▸ hmul⟩, rfl⟩
  apply hπd_not

  have hd_mem : d ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ hd_mem] at heval
  rw [show (algebraMap A B) (f.coeff d) * π ^ d = π ^ d from by rw [hcoeff_d, map_one, one_mul]]
    at heval
  have hπd_eq : π ^ d = -(∑ x ∈ (Finset.range (d + 1)).erase d,
    (algebraMap A B) (f.coeff x) * π ^ x) :=
    eq_neg_of_add_eq_zero_left heval
  rw [hπd_eq]
  apply Submodule.neg_mem

  apply Ideal.sum_mem
  intro i hi
  rw [Finset.mem_erase] at hi
  obtain ⟨hne, hi_range⟩ := hi
  rw [Finset.mem_range] at hi_range
  have hi_lt_d : i < d := by omega

  have hcoeff_mem : f.coeff i ∈ 𝔭 :=
    totally_ramified_minpoly_coeff_mem A K B L π _hπ _htotram hi_lt_d

  have himage_mem : (algebraMap A B) (f.coeff i) ∈ 𝔮 ^ n :=
    hram (Ideal.mem_map_of_mem _ hcoeff_mem)
  by_cases hi0 : i = 0
  ·
    subst hi0
    simp only [pow_zero, mul_one]
    exact Ideal.pow_le_pow_right (by omega) ha₀_mem
  ·
    have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
    exact Ideal.pow_le_pow_right (by omega : n + i ≥ d + 1)
      (pow_add 𝔮 n i ▸ Ideal.mul_mem_mul himage_mem (Ideal.pow_mem_pow hπ_mem i))

theorem totally_ramified_minpoly_coeff0_notMem_sq
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (π : B) (_hπ : Irreducible π)
    (_htotram : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
      Module.finrank K L) :
    (minpoly A π).coeff 0 ∉ (IsLocalRing.maximalIdeal A) ^ 2 := by
  set 𝔭 := IsLocalRing.maximalIdeal A
  set 𝔮 := IsLocalRing.maximalIdeal B
  set n := Module.finrank K L

  have hval := totally_ramified_coeff0_image_not_in_pow_succ A K B L π _hπ _htotram

  intro ha₀_sq
  apply hval

  have h1 : algebraMap A B ((minpoly A π).coeff 0) ∈ Ideal.map (algebraMap A B) (𝔭 ^ 2) :=
    Ideal.mem_map_of_mem _ ha₀_sq
  rw [Ideal.map_pow] at h1

  have hle_ram : Ideal.map (algebraMap A B) 𝔭 ≤ 𝔮 ^ 𝔭.ramificationIdx 𝔮 :=
    Ideal.le_pow_ramificationIdx
  rw [_htotram] at hle_ram

  have h2 : (Ideal.map (algebraMap A B) 𝔭) ^ 2 ≤ (𝔮 ^ n) ^ 2 :=
    Ideal.pow_right_mono hle_ram 2
  rw [← pow_mul, mul_comm] at h2

  have hn_pos : 0 < n := Module.finrank_pos
  have h3 : 𝔮 ^ (2 * n) ≤ 𝔮 ^ (n + 1) := by
    apply Ideal.pow_le_pow_right; omega
  exact h3 (h2 h1)

theorem totally_ramified_minpoly_eisenstein
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (π : B) (hπ : Irreducible π)
    (htotram : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
      Module.finrank K L) :
    (minpoly A π).IsEisensteinAt (IsLocalRing.maximalIdeal A) := by
  have hπ_int : IsIntegral A π := IsIntegral.of_finite A π
  exact (minpoly.monic hπ_int).isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    (fun hn => totally_ramified_minpoly_coeff_mem A K B L π hπ htotram hn)
    (totally_ramified_minpoly_coeff0_notMem_sq A K B L π hπ htotram)

theorem totally_ramified_implies_eisenstein_and_adjoin
    (π : B) (hπ : Irreducible π)
    (htotram : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
      Module.finrank K L) :
    Algebra.adjoin A ({π} : Set B) = ⊤ ∧
    (minpoly A π).IsEisensteinAt (IsLocalRing.maximalIdeal A) :=
  ⟨totally_ramified_adjoin_uniformizer A K B L π hπ htotram,
   totally_ramified_minpoly_eisenstein A K B L π hπ htotram⟩

theorem totally_ramified_iff_eisenstein_adjoin (π : B) (hπ : Irreducible π) :
    ((IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
      Module.finrank K L) ↔
    (Algebra.adjoin A ({π} : Set B) = ⊤ ∧
     (minpoly A π).IsEisensteinAt (IsLocalRing.maximalIdeal A)) := by
  constructor
  · intro htotram
    exact totally_ramified_implies_eisenstein_and_adjoin A K B L π hπ htotram
  · intro ⟨hadj, heis⟩
    exact eisenstein_implies_totally_ramified A K B L π hπ hadj heis

end TotalRamificationEisenstein
