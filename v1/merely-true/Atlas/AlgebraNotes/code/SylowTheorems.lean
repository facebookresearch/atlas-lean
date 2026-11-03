/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral

open Finset Nat MulAction Subgroup

namespace SylowTheorems

theorem sylow_theorems (G : Type*) [Group G] [Fintype G] (p : ℕ) [Fact (Nat.Prime p)] :

    (∃ H : Subgroup G, Nat.card H = p ^ (Nat.card G).factorization p) ∧

    (∀ (P Q : Sylow p G),
      ∃ g : G, P.toSubgroup = Q.toSubgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))) ∧

    (∀ (K : Subgroup G), IsPGroup p K → ∀ (Q : Sylow p G),
      ∃ g : G, K ≤ Q.toSubgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))) ∧

    ((Nat.card (Sylow p G) ∣ Nat.card G / p ^ (Nat.card G).factorization p) ∧
     (Nat.card (Sylow p G) ≡ 1 [MOD p])) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
    exact ⟨P.toSubgroup, Sylow.card_eq_multiplicity P⟩
  ·
    intro P Q
    have := Sylow.isPretransitive_of_finite (p := p) (G := G)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
    exact ⟨g, by rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]; rfl⟩
  ·
    intro K hK Q
    have := Sylow.isPretransitive_of_finite (p := p) (G := G)
    obtain ⟨P, hP⟩ := hK.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
    refine ⟨g, ?_⟩
    have heq : (P : Subgroup G) = Q.toSubgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [← heq]
    exact hP
  ·
    obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
    have hindex : (P : Subgroup G).index = Nat.card G / p ^ (Nat.card G).factorization p := by
      have hcard := P.card_eq_multiplicity
      have h := (P : Subgroup G).card_mul_index
      rw [hcard] at h
      have hpos : (0 : ℕ) < p ^ (Nat.card G).factorization p :=
        Nat.pos_of_ne_zero (pow_ne_zero _ (Nat.Prime.ne_zero (Fact.out)))
      exact (Nat.div_eq_of_eq_mul_right hpos h.symm).symm
    rw [← hindex]
    exact P.card_dvd_index
  ·
    exact card_sylow_modEq_one p G

def IsSylowPSubgroup (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Finite G]
    (H : Subgroup G) : Prop :=
  Nat.card H = p ^ (Nat.card G).factorization p

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

theorem sylow_II (P Q : Sylow p G) :
    ∃ g : G, P.toSubgroup = (Q.toSubgroup).map (MulEquiv.toMonoidHom (MulAut.conj g)) := by
  have := Sylow.isPretransitive_of_finite (p := p) (G := G)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  exact ⟨g, by rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]; rfl⟩

theorem sylow_III (p : ℕ) (G : Type*) [Group G] [Fintype G] [Fact (Nat.Prime p)] :
    (Nat.card (Sylow p G) ∣ Nat.card G / p ^ (Nat.card G).factorization p) ∧
    (Nat.card (Sylow p G) ≡ 1 [MOD p]) := by
  constructor
  · obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
    have hindex : (P : Subgroup G).index = Nat.card G / p ^ (Nat.card G).factorization p := by
      have hcard := P.card_eq_multiplicity
      have h := (P : Subgroup G).card_mul_index
      rw [hcard] at h
      have hpos : (0 : ℕ) < p ^ (Nat.card G).factorization p :=
        Nat.pos_of_ne_zero (pow_ne_zero _ (Nat.Prime.ne_zero (Fact.out)))
      exact (Nat.div_eq_of_eq_mul_right hpos h.symm).symm
    rw [← hindex]
    exact P.card_dvd_index
  · exact card_sylow_modEq_one p G

theorem cauchy_theorem {G : Type*} [Group G] [Fintype G] (p : ℕ) [Fact (Nat.Prime p)]
    (hdvd : p ∣ Fintype.card G) : ∃ x : G, orderOf x = p :=
  exists_prime_orderOf_dvd_card p hdvd

lemma natCast_4_eq_neg1_zmod5 : (Nat.cast 4 : ZMod 5) = -1 := by decide

lemma val_sub_mod_5 (i j : ZMod 5) : (j - i).val = (4 * i.val + j.val) % 5 := by
  have h : j - i = (↑(4 * i.val + j.val) : ZMod 5) := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [natCast_4_eq_neg1_zmod5]; ring
  rw [h, ZMod.val_natCast]

set_option maxHeartbeats 3200000 in
theorem mulEquiv_dihedralGroup_of_not_isCyclic
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) (hnc : ¬IsCyclic G) :
    Nonempty (G ≃* DihedralGroup 5) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card 5 (by omega : (5 : ℕ) ∣ Fintype.card G)
  obtain ⟨y, hy2⟩ := exists_prime_orderOf_dvd_card 2 (by omega : (2 : ℕ) ∣ Fintype.card G)
  have hy_sq : y * y = 1 := by
    simpa [sq] using (show y ^ 2 = 1 from by rw [← hy2]; exact pow_orderOf_eq_one y)
  have hy_inv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy_sq

  have hconj : y * x * y⁻¹ = x ^ 4 := by
    have hx_pgroup : IsPGroup 5 (Subgroup.zpowers x) :=
      IsPGroup.iff_card.mpr ⟨1, by rw [pow_one, Nat.card_zpowers, hx5]⟩
    obtain ⟨P5, hP5⟩ := hx_pgroup.exists_le_sylow
    haveI : Subsingleton (Sylow 5 G) := by
      have hmod := card_sylow_modEq_one 5 G
      have hdvd := P5.card_dvd_index
      have hcG : Nat.card G = 10 := by rwa [Nat.card_eq_fintype_card]
      have hcP : Nat.card (P5 : Subgroup G) = 5 := by
        have h := P5.card_eq_multiplicity; rw [hcG] at h
        norm_num [show (Nat.factorization 10) 5 = 1 from by
          rw [show (10 : ℕ) = 2 * 5 from by norm_num,
            Nat.factorization_mul (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (5 : ℕ) ≠ 0)]
          simp only [Finsupp.add_apply]
          rw [Nat.Prime.factorization_self (by decide : Nat.Prime 5),
            show (Nat.factorization 2) 5 = 0 from
              Nat.factorization_eq_zero_of_not_dvd (by decide : ¬(5 ∣ 2))]] at h
        rw [Nat.card_eq_fintype_card]; omega
      have hindex : (P5 : Subgroup G).index = 2 := by
        have h := (P5 : Subgroup G).card_mul_index; rw [hcP, hcG] at h; omega
      rw [hindex] at hdvd
      have hone : Nat.card (Sylow 5 G) = 1 := by
        have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
        have h12 := Nat.le_of_dvd (by omega) hdvd
        rcases (show _ ∨ _ from by omega : Nat.card (Sylow 5 G) = 1 ∨ Nat.card (Sylow 5 G) = 2) with h | h
        · exact h
        · exfalso; rw [h] at hmod; simp [Nat.ModEq] at hmod
      exact (Nat.card_eq_one_iff_unique.mp hone).1
    have hP5_normal : (P5 : Subgroup G).Normal := Sylow.normal_of_subsingleton P5
    have hczp : Nat.card (Subgroup.zpowers x) = 5 := by rw [Nat.card_zpowers, hx5]
    have hcP5 : Nat.card (P5 : Subgroup G) = 5 := by
      have hcG : Nat.card G = 10 := by rwa [Nat.card_eq_fintype_card]
      have h := P5.card_eq_multiplicity; rw [hcG] at h
      norm_num [show (Nat.factorization 10) 5 = 1 from by
        rw [show (10 : ℕ) = 2 * 5 from by norm_num,
          Nat.factorization_mul (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (5 : ℕ) ≠ 0)]
        simp only [Finsupp.add_apply]
        rw [Nat.Prime.factorization_self (by decide : Nat.Prime 5),
          show (Nat.factorization 2) 5 = 0 from
            Nat.factorization_eq_zero_of_not_dvd (by decide : ¬(5 ∣ 2))]] at h
      rw [Nat.card_eq_fintype_card]; omega
    have hzp_eq_P5 : Subgroup.zpowers x = (P5 : Subgroup G) := by
      apply le_antisymm hP5
      have hcard : Nat.card (P5 : Subgroup G) ≤ Nat.card (Subgroup.zpowers x) := by
        rw [hcP5, hczp]
      have hinj : Function.Injective (Subgroup.inclusion hP5) := Subgroup.inclusion_injective hP5
      rw [show (P5 : Subgroup G) ≤ Subgroup.zpowers x ↔ ∀ g, g ∈ (P5 : Subgroup G) → g ∈ Subgroup.zpowers x from Iff.rfl]
      intro g hg
      have hbij : Function.Bijective (Subgroup.inclusion hP5) := by
        rw [Fintype.bijective_iff_injective_and_card]
        exact ⟨hinj, by simp only [Nat.card_eq_fintype_card] at hczp hcP5; omega⟩
      obtain ⟨⟨g', hg'⟩, heq⟩ := hbij.2 ⟨g, hg⟩
      have : g' = g := congr_arg Subtype.val heq
      rw [← this]; exact hg'
    have hconj_mem : y * x * y⁻¹ ∈ Subgroup.zpowers x := by
      rw [hzp_eq_P5]; exact hP5_normal.conj_mem x (hP5 (Subgroup.mem_zpowers x)) y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconj_mem

    have hkk : x ^ (k * k) = x := by
      have hphi : y * x ^ k * y⁻¹ = (y * x * y⁻¹) ^ k := conj_zpow.symm
      rw [hk.symm, ← zpow_mul] at hphi


      have hphi2 : y * (y * x * y⁻¹) * y⁻¹ = x := by
        rw [hy_inv]
        calc y * (y * x * y) * y = (y * y) * x * (y * y) := by group
          _ = x := by rw [hy_sq, one_mul, mul_one]


      rw [hk] at hphi

      rw [hphi2] at hphi

      exact hphi.symm

    have h5dvd : (5 : ℤ) ∣ k * k - 1 := by
      have h1 : x ^ (k * k - 1) = 1 := by
        have : x ^ (k * k) * x⁻¹ = 1 := by rw [hkk, mul_inv_cancel]
        rwa [← zpow_neg_one, ← zpow_add] at this
      have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rw [hx5] at h2; exact_mod_cast h2
    have hk_mod : k % 5 = 1 ∨ k % 5 = 4 := by
      have hmod5 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
      have hkey : (k % 5) * (k % 5) % 5 = 1 := by
        have h3 : (k * k) % 5 = 1 := by omega
        have h4 : (k * k) % 5 = (k % 5 * (k % 5)) % 5 := Int.mul_emod k k 5
        omega
      rcases hmod5 with h | h | h | h | h <;> simp_all
    rcases hk_mod with hk1 | hk4
    ·
      exfalso; apply hnc
      have hyx_eq_x : y * x * y⁻¹ = x := by
        rw [← hk]; conv_lhs => rw [← zpow_mod_orderOf x k]
        rw [hx5]; simp only [Nat.cast_ofNat]
        rw [show k % (5 : ℤ) = 1 from hk1]; simp
      have hcomm : Commute x y := by
        have h : x * y = y * x := by
          have h1 : y * x * y⁻¹ = x := hyx_eq_x
          have h2 : y * x = x * y := by
            calc y * x = y * x * y⁻¹ * y := by rw [inv_mul_cancel_right]
              _ = x * y := by rw [h1]
          exact h2.symm
        exact h
      have hord : orderOf (x * y) = 10 := by
        have := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx5, hy2]; norm_num)
        rw [hx5, hy2] at this; exact this
      exact isCyclic_of_orderOf_eq_card (x * y) (by rw [hord, Nat.card_eq_fintype_card, hG])
    ·
      rw [← hk]; conv_lhs => rw [← zpow_mod_orderOf x k]
      rw [hx5]; simp only [Nat.cast_ofNat]
      rw [show k % (5 : ℤ) = 4 from hk4]
      norm_num
      exact zpow_natCast x 4

  have hconj_n : ∀ n : ℕ, y * x ^ n * y⁻¹ = x ^ (4 * n) := by
    intro n; induction n with
    | zero => simp [mul_inv_cancel]
    | succ n ih =>
      calc y * x ^ (n + 1) * y⁻¹
          = (y * x ^ n * y⁻¹) * (y * x * y⁻¹) := by rw [pow_succ]; group
        _ = x ^ (4 * n + 4) := by rw [ih, hconj, pow_add]
        _ = x ^ (4 * (n + 1)) := by ring_nf
  have hcomm_n : ∀ n : ℕ, x ^ n * y = y * x ^ (4 * n) := by
    intro n
    have h := hconj_n n; rw [hy_inv] at h
    have h2 : y * (y * x ^ n * y) = y * x ^ (4 * n) := congr_arg (y * ·) h
    simp only [← mul_assoc] at h2; rw [hy_sq, one_mul] at h2; exact h2
  let f : DihedralGroup 5 →* G := {
    toFun := fun g => match g with | .r i => x ^ i.val | .sr i => y * x ^ i.val
    map_one' := by show x ^ (0 : ZMod 5).val = 1; simp
    map_mul' := by
      intro a b; match a, b with
      | .r i, .r j =>
        show x ^ (i + j).val = x ^ i.val * x ^ j.val
        rw [← pow_add, ZMod.val_add]
        have h := @pow_mod_orderOf _ _ x (i.val + j.val); rw [hx5] at h; exact h
      | .r i, .sr j =>
        show y * x ^ (j - i).val = x ^ i.val * (y * x ^ j.val)
        rw [← mul_assoc, hcomm_n i.val, mul_assoc, ← pow_add]
        congr 1; rw [val_sub_mod_5 i j]
        have h := @pow_mod_orderOf _ _ x (4 * i.val + j.val); rw [hx5] at h; exact h
      | .sr i, .r j =>
        show y * x ^ (i + j).val = (y * x ^ i.val) * x ^ j.val
        rw [mul_assoc]; congr 1
        rw [← pow_add, ZMod.val_add]
        have h := @pow_mod_orderOf _ _ x (i.val + j.val); rw [hx5] at h; exact h
      | .sr i, .sr j =>
        show x ^ (j - i).val = (y * x ^ i.val) * (y * x ^ j.val)
        symm
        calc (y * x ^ i.val) * (y * x ^ j.val)
            = y * (x ^ i.val * y) * x ^ j.val := by group
          _ = y * (y * x ^ (4 * i.val)) * x ^ j.val := by rw [hcomm_n]
          _ = (y * y) * x ^ (4 * i.val + j.val) := by group
          _ = x ^ (4 * i.val + j.val) := by rw [hy_sq, one_mul]
          _ = x ^ ((4 * i.val + j.val) % 5) := by
              have h := @pow_mod_orderOf _ _ x (4 * i.val + j.val); rw [hx5] at h; exact h.symm
          _ = x ^ (j - i).val := by congr 1; exact (val_sub_mod_5 i j).symm
  }
  have hf_bij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [DihedralGroup.card, hG]⟩
    intro a b hab
    match a, b with
    | .r i, .r j =>
      have h : x ^ i.val = x ^ j.val := hab
      have h_inj := pow_injOn_Iio_orderOf (G := G) (x := x); rw [hx5] at h_inj
      exact congr_arg _ (Fin.ext (h_inj (Set.mem_Iio.mpr (ZMod.val_lt i))
        (Set.mem_Iio.mpr (ZMod.val_lt j)) h))
    | .sr i, .sr j =>
      have h2 : x ^ i.val = x ^ j.val := mul_left_cancel (show y * x ^ i.val = y * x ^ j.val from hab)
      have h_inj := pow_injOn_Iio_orderOf (G := G) (x := x); rw [hx5] at h_inj
      exact congr_arg _ (Fin.ext (h_inj (Set.mem_Iio.mpr (ZMod.val_lt i))
        (Set.mem_Iio.mpr (ZMod.val_lt j)) h2))
    | .r i, .sr j =>
      exfalso
      have h : x ^ i.val = y * x ^ j.val := hab
      have hy_in : y ∈ Subgroup.zpowers x := by
        have : y = x ^ i.val * (x ^ j.val)⁻¹ := by
          have := congr_arg (· * (x ^ j.val)⁻¹) h; simp [mul_assoc] at this; exact this.symm
        rw [this]; exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)
          (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
      have := Subgroup.orderOf_dvd_natCard _ hy_in
      rw [Nat.card_zpowers, hx5, hy2] at this; omega
    | .sr i, .r j =>
      exfalso
      have h : y * x ^ i.val = x ^ j.val := hab
      have hy_in : y ∈ Subgroup.zpowers x := by
        have : y = x ^ j.val * (x ^ i.val)⁻¹ := by
          have := congr_arg (· * (x ^ i.val)⁻¹) h; simp [mul_assoc] at this; exact this
        rw [this]; exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)
          (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
      have := Subgroup.orderOf_dvd_natCard _ hy_in
      rw [Nat.card_zpowers, hx5, hy2] at this; omega
  exact ⟨(MulEquiv.ofBijective f hf_bij).symm⟩

theorem groups_of_order_10_classification
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) :
    Nonempty (G ≃* Multiplicative (ZMod 10)) ∨ Nonempty (G ≃* DihedralGroup 5) := by
  by_cases hcyc : IsCyclic G
  · left
    have hcard : Nat.card G = 10 := by rwa [Nat.card_eq_fintype_card]
    have e := zmodCyclicMulEquiv hcyc
    rw [hcard] at e
    exact ⟨e.symm⟩
  · right
    exact mulEquiv_dihedralGroup_of_not_isCyclic G hG hcyc

theorem card_stabilizer_dvd_card {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (U : Finset G)
    (hU : ∀ (h : G), h ∈ H → ∀ u ∈ U, h * u ∈ U) :
    Nat.card H ∣ U.card := by
  classical
  haveI : Fintype H := Subtype.fintype (· ∈ H)
  rw [Nat.card_eq_fintype_card]
  let orb : G → Finset G := fun u => Finset.univ.image (fun h : H => (h : G) * u)
  have orbit_card : ∀ u : G, (orb u).card = Fintype.card H := by
    intro u
    apply Finset.card_image_of_injective
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Subtype.mk.injEq]
    exact mul_right_cancel (show a * u = b * u from by simpa using hab)
  have orbit_sub : ∀ u ∈ U, orb u ⊆ U := by
    intro u hu v hv
    simp only [orb, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨⟨h, hh⟩, rfl⟩ := hv
    exact hU h hh u hu
  have orbit_eq : ∀ u v : G, v ∈ orb u → orb v = orb u := by
    intro u v hv
    simp only [orb, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨⟨h₀, hh₀⟩, rfl⟩ := hv
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h₁, hh₁⟩, rfl⟩
      exact ⟨⟨h₁ * h₀, H.mul_mem hh₁ hh₀⟩, by simp [mul_assoc]⟩
    · rintro ⟨⟨h₁, hh₁⟩, rfl⟩
      exact ⟨⟨h₁ * h₀⁻¹, H.mul_mem hh₁ (H.inv_mem hh₀)⟩, by simp [mul_assoc]⟩
  have mem_orbit : ∀ u : G, u ∈ orb u := by
    intro u
    simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨1, H.one_mem⟩, by simp⟩
  have fiber_eq_orbit : ∀ u ∈ U, U.filter (fun v => orb v = orb u) = orb u := by
    intro u hu
    ext v
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨_, hv⟩
      rw [← hv]
      exact mem_orbit v
    · intro hv
      exact ⟨orbit_sub u hu hv, orbit_eq u v hv⟩
  have h_fiber : U.card = ∑ O ∈ U.image orb, (U.filter (fun v => orb v = O)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro u hu
    exact Finset.mem_image_of_mem orb hu
  have h_each : ∀ O ∈ U.image orb, (U.filter (fun v => orb v = O)).card = Fintype.card H := by
    intro O hO
    simp only [Finset.mem_image] at hO
    obtain ⟨u, hu, rfl⟩ := hO
    rw [fiber_eq_orbit u hu, orbit_card u]
  rw [h_fiber, Finset.sum_congr rfl h_each, Finset.sum_const, smul_eq_mul]
  exact dvd_mul_left _ _

def poles (G : Type*) (X : Type*) [Group G] [MulAction G X] : Set X :=
  {x : X | ∃ g : G, g ≠ 1 ∧ g • x = x}

theorem smul_mem_poles {G : Type*} {X : Type*} [Group G] [MulAction G X]
    (g : G) (p : X) (hp : p ∈ poles G X) : g • p ∈ poles G X := by
  obtain ⟨h, hne, hfix⟩ := hp
  refine ⟨g * h * g⁻¹, ?_, ?_⟩
  · intro heq
    apply hne
    have : h = g⁻¹ * (g * h * g⁻¹) * g := by group
    rw [this, heq, mul_one, inv_mul_cancel]
  · calc (g * h * g⁻¹) • (g • p)
        = g • (h • (g⁻¹ • (g • p))) := by rw [mul_smul, mul_smul]
      _ = g • (h • p) := by rw [inv_smul_smul]
      _ = g • p := by rw [hfix]
